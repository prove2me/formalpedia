-- Prove2me | solution 1 for EditMulticoloring.Code.decoder_correctness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:02:11.207372+00:00
-- url     : https://prove2.me/submissions/e195a0b5-b1e5-41bd-939c-7e42b63704ab

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Theorems.Thm_EditMulticoloring_Code_polynomial_coloring
import Theorems.Thm_EditMulticoloring_Code_edit_ball_volume
import Theorems.Thm_EditMulticoloring_Code_prime_multicoloring
import Theorems.Thm_EditMulticoloring_Code_short_edit_code
import Theorems.Thm_EditMulticoloring_Code_interval_restriction

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Decoder
open EditMulticoloring.Code Polynomial

/-! ## Bit polynomials over `ZMod 2` -/

def bit (a i : ℕ) : ZMod 2 := if a.testBit i then 1 else 0

lemma cast_div_mod (a i : ℕ) : (((a / 2 ^ i) % 2 : ℕ) : ZMod 2) = bit a i := by
  unfold bit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with h | h <;> simp [h]

lemma bit_eq_zero_of_lt {a i : ℕ} (h : a < 2 ^ i) : bit a i = 0 := by
  simp [bit, Nat.testBit_lt_two_pow h]

lemma coeff_bp (a i : ℕ) : (binaryPoly a).coeff i = bit a i := by
  unfold binaryPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one, cast_div_mod]
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hi
    simp only [Finset.mem_range, not_lt] at hi
    have : a < 2 ^ i := lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) hi)
    rw [if_pos rfl, mul_one, cast_div_mod, bit_eq_zero_of_lt this]

lemma bp_zero : binaryPoly 0 = 0 := by
  ext i; simp [coeff_bp, bit]

lemma bp_xor (a b : ℕ) : binaryPoly (Nat.xor a b) = binaryPoly a + binaryPoly b := by
  ext i
  rw [Polynomial.coeff_add, coeff_bp, coeff_bp, coeff_bp]
  unfold bit
  rw [show Nat.xor a b = a ^^^ b from rfl, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

lemma bp_shift (a k : ℕ) : binaryPoly (a * 2 ^ k) = binaryPoly a * X ^ k := by
  ext i
  rw [Polynomial.coeff_mul_X_pow', coeff_bp]
  unfold bit
  rw [Nat.testBit_mul_two_pow]
  split_ifs with h1 h2 h2 <;> simp_all [coeff_bp, bit]

lemma bp_eq_sum (b : ℕ) :
    binaryPoly b = ∑ i ∈ Finset.range (b.log2 + 1), C (bit b i) * X ^ i := by
  unfold binaryPoly
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cast_div_mod]

lemma binaryMul_fold (a b : ℕ) : ∀ N : ℕ,
    binaryPoly ((List.range N).foldl (fun z i =>
      if b.testBit i then Nat.xor z (a * 2 ^ i) else z) 0) =
      binaryPoly a * ∑ i ∈ Finset.range N, C (bit b i) * X ^ i := by
  intro N
  induction N with
  | zero => simp [bp_zero]
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs with h
    · rw [bp_xor, bp_shift, ih]
      simp [bit, h]; ring
    · rw [ih]; simp [bit, h]

lemma bp_binaryMul (a b : ℕ) : binaryPoly (binaryMul a b) = binaryPoly a * binaryPoly b := by
  unfold binaryMul
  rw [binaryMul_fold, bp_eq_sum b]

/-! ## Reduction -/

lemma binaryRem_cong (p : ℕ) : ∀ (l : List ℕ) (z : ℕ), ∃ c : (ZMod 2)[X],
    binaryPoly (l.foldl (fun z i =>
      if p ≠ 0 ∧ p.log2 ≤ i ∧ z.testBit i then
        Nat.xor z (p * 2 ^ (i - p.log2)) else z) z) = binaryPoly z + binaryPoly p * c := by
  intro l
  induction l with
  | nil => intro z; exact ⟨0, by simp⟩
  | cons i l ih =>
    intro z
    simp only [List.foldl_cons]
    split_ifs with h
    · obtain ⟨c, hc⟩ := ih (Nat.xor z (p * 2 ^ (i - p.log2)))
      refine ⟨c + X ^ (i - p.log2), ?_⟩
      rw [hc, bp_xor, bp_shift]; ring
    · exact ih z

lemma testBit_log2 {p : ℕ} (hp : p ≠ 0) : p.testBit p.log2 = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 := Nat.log2_self_le hp
  have h2 : p < 2 ^ p.log2 * 2 := by rw [← pow_succ]; exact Nat.lt_log2_self
  have : p / 2 ^ p.log2 = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [this]

lemma binaryRem_bits (p : ℕ) (hp : p ≠ 0) : ∀ (N z : ℕ),
    (∀ j, N ≤ j → p.log2 ≤ j → z.testBit j = false) →
    ∀ j, p.log2 ≤ j → ((List.range N).reverse.foldl (fun z i =>
      if p ≠ 0 ∧ p.log2 ≤ i ∧ z.testBit i then
        Nat.xor z (p * 2 ^ (i - p.log2)) else z) z).testBit j = false := by
  intro N
  induction N with
  | zero => intro z hz j hj; simpa using hz j (Nat.zero_le _) hj
  | succ N ih =>
    intro z hz
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.foldl_cons]
    apply ih
    intro j hNj hpj
    split_ifs with h
    · rw [show Nat.xor z (p * 2 ^ (N - p.log2)) = z ^^^ (p * 2 ^ (N - p.log2)) from rfl,
        Nat.testBit_xor, Nat.testBit_mul_two_pow]
      rcases Nat.eq_or_lt_of_le hNj with hj | hj
      · subst hj
        rw [h.2.2, show N - (N - p.log2) = p.log2 by omega, testBit_log2 hp]
        simp
      · rw [hz j (by omega) hpj]
        have : p < 2 ^ (j - (N - p.log2)) :=
          lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [Nat.testBit_lt_two_pow this]
    · rcases Nat.eq_or_lt_of_le hNj with hj | hj
      · subst hj
        simp only [ne_eq, hp, not_false_eq_true, true_and, not_and, Bool.not_eq_true] at h
        exact h hpj
      · exact hz j (by omega) hpj

lemma binaryRem_lt (p a : ℕ) (hp : p ≠ 0) : binaryRem p a < 2 ^ p.log2 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold binaryRem
  apply binaryRem_bits p hp _ a _ j hj
  intro i hi _
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_log2_self
    (Nat.pow_le_pow_right (by norm_num) hi))

lemma fieldMul_lt (p a b : ℕ) (hp : p ≠ 0) : fieldMul p a b < 2 ^ p.log2 :=
  binaryRem_lt p _ hp

/-! ## The field `AdjoinRoot (binaryPoly p)` -/

noncomputable def phi (p n : ℕ) : AdjoinRoot (binaryPoly p) :=
  AdjoinRoot.mk (binaryPoly p) (binaryPoly n)

lemma phi_zero (p : ℕ) : phi p 0 = 0 := by simp [phi, bp_zero]

lemma phi_xor (p a b : ℕ) : phi p (Nat.xor a b) = phi p a + phi p b := by
  unfold phi; rw [bp_xor, map_add]

lemma phi_fieldMul (p a b : ℕ) : phi p (fieldMul p a b) = phi p a * phi p b := by
  unfold phi fieldMul binaryRem
  obtain ⟨c, hc⟩ := binaryRem_cong p (List.range ((binaryMul a b).log2 + 1)).reverse (binaryMul a b)
  rw [hc, bp_binaryMul]
  simp

lemma log2_of_valid {b p : ℕ} (hp : ValidModulus b p) : p.log2 = b ∧ p ≠ 0 := by
  obtain ⟨_, h1, h2, _⟩ := hp
  have hp0 : p ≠ 0 := by have := Nat.one_le_two_pow (n := b); omega
  exact ⟨(Nat.log2_eq_iff hp0).2 ⟨h1, h2⟩, hp0⟩

lemma bp_inj {x y : ℕ} (h : binaryPoly x = binaryPoly y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun f => Polynomial.coeff f i) h
  simp only [coeff_bp, bit] at this
  cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

lemma phi_inj {b p : ℕ} (hp : ValidModulus b p) {x y : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b)
    (h : phi p x = phi p y) : x = y := by
  obtain ⟨hlog, hp0⟩ := log2_of_valid hp
  unfold phi at h
  rw [← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero] at h
  apply bp_inj
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_dvd_of_degree_lt h
  have hdeg : (b : WithBot ℕ) ≤ (binaryPoly p).degree := by
    apply Polynomial.le_degree_of_ne_zero
    rw [coeff_bp, bit, ← hlog, testBit_log2 hp0]
    simp
  refine lt_of_lt_of_le ?_ hdeg
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [Polynomial.coeff_sub, coeff_bp, coeff_bp,
    bit_eq_zero_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hm)),
    bit_eq_zero_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hm)), sub_zero]

lemma natDegree_bp {b p : ℕ} (hp : ValidModulus b p) : (binaryPoly p).natDegree = b := by
  obtain ⟨hlog, hp0⟩ := log2_of_valid hp
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_bp]
    apply bit_eq_zero_of_lt
    have : p < 2 ^ (b + 1) := hp.2.2.1
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by exact_mod_cast hm))
  · rw [coeff_bp, bit, ← hlog, testBit_log2 hp0]; simp

lemma bp_ne_zero {b p : ℕ} (hp : ValidModulus b p) : binaryPoly p ≠ 0 := by
  obtain ⟨hlog, hp0⟩ := log2_of_valid hp
  intro h
  have := congrArg (fun f => Polynomial.coeff f p.log2) h
  simp [coeff_bp, bit, testBit_log2 hp0] at this

lemma card_adjoin {b p : ℕ} (hp : ValidModulus b p) :
    Nat.card (AdjoinRoot (binaryPoly p)) = 2 ^ b ∧ Finite (AdjoinRoot (binaryPoly p)) := by
  let B := AdjoinRoot.powerBasisAux (bp_ne_zero hp)
  have e := B.equivFun.toEquiv
  refine ⟨?_, Finite.of_equiv _ e.symm⟩
  rw [Nat.card_congr e, Nat.card_fun, natDegree_bp hp]
  simp

lemma phi_bij {b p : ℕ} (hp : ValidModulus b p) :
    Function.Bijective (fun k : Fin (2 ^ b) => phi p k.val) := by
  obtain ⟨hc, hf⟩ := card_adjoin hp
  apply Function.Injective.bijective_of_nat_card_le
  · intro x y h
    exact Fin.ext (phi_inj hp x.isLt y.isLt h)
  · rw [hc]; simp

/-- Horner evaluation. -/
lemma phi_horner (Q p id a : ℕ) : ∀ (N z : ℕ),
    phi p ((List.range N).reverse.foldl (fun z i =>
      Nat.xor (fieldMul p z a) ((id / Q ^ i) % Q)) z) =
      phi p z * phi p a ^ N + ∑ i ∈ Finset.range N, phi p ((id / Q ^ i) % Q) * phi p a ^ i := by
  intro N
  induction N with
  | zero => intro z; simp
  | succ N ih =>
    intro z
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.foldl_cons]
    rw [ih, phi_xor, phi_fieldMul, Finset.sum_range_succ]
    ring

lemma bitEval_lt {b p : ℕ} (hp : ValidModulus b p) (K id a : ℕ) :
    bitEval (2 ^ b) p K id a < 2 ^ b := by
  obtain ⟨hlog, hp0⟩ := log2_of_valid hp
  unfold bitEval
  suffices ∀ (l : List ℕ) (z : ℕ), z < 2 ^ b → l.foldl (fun z i =>
      Nat.xor (fieldMul p z a) ((id / (2 ^ b) ^ i) % (2 ^ b))) z < 2 ^ b from
    this _ 0 (by positivity)
  intro l
  induction l with
  | nil => intro z hz; simpa using hz
  | cons i l ih =>
    intro z _
    apply ih
    have h1 := fieldMul_lt p z a hp0
    rw [hlog] at h1
    exact Nat.xor_lt_two_pow h1 (Nat.mod_lt _ (by positivity))

/-- The separating evaluation point from `polynomial_coloring`, transported to `bitEval`. -/
theorem bit_separating {V : Type} [Fintype V]
    (G : SimpleGraph V) (r K : ℕ) (hr : 1 ≤ r) (hK : 1 ≤ K)
    (degree : ∀ v, (neighbors G v).card ≤ r)
    (id : V → ℕ) (hid : Function.Injective id) (range : ∀ v, id v < 2 ^ K)
    (p : ℕ) (hp : ValidModulus (ceilLog 2 (r * K + 1)) p) (v : V) :
    ∃ α < fieldSize r K, ∀ u, G.Adj v u →
      bitEval (fieldSize r K) p K (id v) α ≠ bitEval (fieldSize r K) p K (id u) α := by
  set b := ceilLog 2 (r * K + 1) with hb
  have hQ : fieldSize r K = 2 ^ b := rfl
  have : Fact (Irreducible (binaryPoly p)) := ⟨hp.2.2.2⟩
  let e : AdjoinRoot (binaryPoly p) ≃ Fin (fieldSize r K) :=
    (Equiv.ofBijective _ (phi_bij hp)).symm
  have he : ∀ k : Fin (fieldSize r K), e.symm k = phi p k.val := fun k => rfl
  have hQpos : 0 < fieldSize r K := by rw [hQ]; positivity
  -- identifier polynomial evaluation agrees with bitEval
  have heval : ∀ (n : ℕ) (a : AdjoinRoot (binaryPoly p)),
      (identifierPoly e K n).eval a =
        phi p (bitEval (fieldSize r K) p K n (e a).val) := by
    intro n a
    have ha : phi p (e a).val = a := by rw [← he]; simp
    unfold bitEval
    rw [phi_horner, phi_zero, zero_mul, zero_add, ha]
    unfold identifierPoly
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    congr 1
    unfold fieldElement
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using Nat.mod_lt _ hQpos)]
    simp [he]
  obtain ⟨a, ha⟩ := ((polynomial_coloring G r K hr hK degree id hid range e).1 v)
  refine ⟨(e a).val, (e a).isLt, fun u hu h => ha u hu ?_⟩
  rw [heval, heval, h]

end EditMulticoloring.Dev.Decoder
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Decoder
open EditMulticoloring.Code OAI.EditDistortion

/-! ## Edit metric -/

theorem script_trans {Al : Type} {n m : ℕ} {x y z : List Al}
    (h1 : Script true n x y) (h2 : Script true m y z) : Script true (n + m) x z := by
  induction h1 with
  | nil => rw [Nat.zero_add]; exact h2
  | cons first rest ih =>
    rw [Nat.add_right_comm]
    exact Script.cons first (ih h2)

theorem step_symm {Al : Type} {x y : List Al} (h : Step true x y) : Step true y x := by
  cases h with
  | insert p q a => exact Step.delete p q a
  | delete p q a => exact Step.insert p q a
  | substitute hs p q a b => exact Step.substitute hs p q b a

theorem script_symm {Al : Type} {n : ℕ} {x y : List Al}
    (h : Script true n x y) : Script true n y x := by
  induction h with
  | nil => exact Script.nil _
  | cons first rest ih =>
    exact script_trans ih (Script.cons (step_symm first) (Script.nil _))

theorem script_to_nil {Al : Type} (x : List Al) : Script true x.length x [] := by
  induction x with
  | nil => exact Script.nil _
  | cons a x ih =>
    have := Step.delete (substitutions := true) [] x a
    simp only [List.nil_append] at this
    exact Script.cons this ih

theorem script_exists {Al : Type} (x y : List Al) : ∃ n, Script true n x y :=
  ⟨_, script_trans (script_to_nil x) (script_symm (script_to_nil y))⟩

theorem edit_attained {Al : Type} (x y : List Al) :
    Script true (edit x y) x y :=
  Nat.sInf_mem (s := {n | Script true n x y}) (script_exists x y)

theorem edit_le {Al : Type} {n : ℕ} {x y : List Al} (h : Script true n x y) :
    edit x y ≤ n := Nat.sInf_le h

theorem dist_symm {q : ℕ} (x y : Word q) : distance x y = distance y x := by
  unfold distance
  exact le_antisymm (edit_le (script_symm (edit_attained y x)))
    (edit_le (script_symm (edit_attained x y)))

theorem dist_triangle {q : ℕ} (x y z : Word q) :
    distance x z ≤ distance x y + distance y z := by
  unfold distance
  exact edit_le (script_trans (edit_attained x y) (edit_attained y z))

theorem script_length {Al : Type} {n : ℕ} {x y : List Al} (h : Script true n x y) :
    y.length ≤ x.length + n ∧ x.length ≤ y.length + n := by
  induction h with
  | nil x => simp
  | @cons n x w z first rest ih =>
    have : w.length ≤ x.length + 1 ∧ x.length ≤ w.length + 1 := by
      cases first <;> simp <;> omega
    omega

theorem dist_length {q : ℕ} (x y : Word q) :
    y.length ≤ x.length + distance x y ∧ x.length ≤ y.length + distance x y :=
  script_length (edit_attained x y)

theorem script_split {Al : Type} : ∀ (k l : ℕ) (x y : List Al), Script true (k + l) x y →
    ∃ z, Script true k x z ∧ Script true l z y := by
  intro k
  induction k with
  | zero => intro l x y h; exact ⟨x, Script.nil x, by simpa using h⟩
  | succ k ih =>
    intro l x y h
    rw [show k + 1 + l = (k + l) + 1 by omega] at h
    cases h with
    | cons first rest =>
      obtain ⟨z, h1, h2⟩ := ih l _ y rest
      exact ⟨z, Script.cons first h1, h2⟩

theorem midpoint {q : ℕ} (t : ℕ) (x y : Word q) (h : distance x y ≤ 2 * t) :
    ∃ z, distance x z ≤ t ∧ distance z y ≤ t := by
  have hs := edit_attained x y
  set d := edit x y
  have hd : d ≤ 2 * t := h
  rw [show d = min d t + (d - min d t) by omega] at hs
  obtain ⟨z, h1, h2⟩ := script_split _ _ x y hs
  refine ⟨z, ?_, ?_⟩
  · exact le_trans (edit_le h1) (min_le_right _ _)
  · exact le_trans (edit_le h2) (by omega)

/-! ## Words -/

theorem value_snoc {q : ℕ} (l : Word q) (a : Fin q) :
    value (l ++ [a]) = q * value l + a.val := by
  simp [value, List.foldl_append]

theorem value_ofFn_succ {q n : ℕ} (u : Fin (n + 1) → Fin q) :
    value (List.ofFn u) = q * value (List.ofFn (fun i : Fin n => u i.castSucc)) + (u (Fin.last n)).val := by
  rw [List.ofFn_succ', List.concat_eq_append, value_snoc]

theorem value_ofFn_lt {q : ℕ} (hq : 0 < q) : ∀ {n : ℕ} (u : Fin n → Fin q),
    value (List.ofFn u) < q ^ n := by
  intro n
  induction n with
  | zero => intro u; simp [value]
  | succ n ih =>
    intro u
    rw [value_ofFn_succ, pow_succ]
    have h1 := ih (fun i : Fin n => u i.castSucc)
    have h2 := (u (Fin.last n)).isLt
    calc _ < q * value (List.ofFn (fun i : Fin n => u i.castSucc)) + q := by omega
      _ = q * (value (List.ofFn (fun i : Fin n => u i.castSucc)) + 1) := by ring
      _ ≤ q * q ^ n := Nat.mul_le_mul_left _ h1
      _ = q ^ n * q := mul_comm _ _

theorem value_ofFn_inj {q : ℕ} (hq : 0 < q) : ∀ {n : ℕ} (u v : Fin n → Fin q),
    value (List.ofFn u) = value (List.ofFn v) → u = v := by
  intro n
  induction n with
  | zero => intro u v _; funext i; exact i.elim0
  | succ n ih =>
    intro u v h
    rw [value_ofFn_succ, value_ofFn_succ] at h
    have hx := (u (Fin.last n)).isLt
    have hy := (v (Fin.last n)).isLt
    set a := value (List.ofFn (fun i : Fin n => u i.castSucc))
    set b := value (List.ofFn (fun i : Fin n => v i.castSucc))
    have d1 : (q * a + (u (Fin.last n)).val) / q = (q * b + (v (Fin.last n)).val) / q := by rw [h]
    have d2 : (q * a + (u (Fin.last n)).val) % q = (q * b + (v (Fin.last n)).val) % q := by rw [h]
    rw [Nat.mul_add_div hq, Nat.mul_add_div hq, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy] at d1
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at d2
    have ha : a = b := by omega
    have hpre := ih (fun i : Fin n => u i.castSucc) (fun i : Fin n => v i.castSucc) ha
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.ext d2
    · exact congrFun hpre j

def ofWord {q m : ℕ} (y : Word q) (h : y.length = m) : FixedWord q m :=
  fun i => y[i.val]'(by rw [h]; exact i.isLt)

theorem toWord_ofWord {q m : ℕ} (y : Word q) (h : y.length = m) : toWord (ofWord y h) = y := by
  subst h
  unfold toWord ofWord
  exact List.ofFn_getElem

theorem toWord_inj {q m : ℕ} : Function.Injective (toWord : FixedWord q m → Word q) :=
  List.ofFn_injective

theorem length_toWord {q m : ℕ} (x : FixedWord q m) : (toWord x).length = m := by
  simp [toWord]

theorem le_two_pow_ceilLog (q : ℕ) (hq : 2 ≤ q) : q ≤ 2 ^ ceilLog 2 q ∧ 1 ≤ ceilLog 2 q := by
  have h : q ≤ 2 ^ ceilLog 2 q := by
    unfold ceilLog floorLog
    dsimp only
    split_ifs with h
    · exact h
    · exact le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) q)
  refine ⟨h, ?_⟩
  by_contra h0
  push Not at h0
  have : ceilLog 2 q = 0 := by omega
  rw [this] at h; simp at h; omega

theorem radiusBound_mono (q s : ℕ) {a b : ℕ} (h : a ≤ b) : radiusBound q s a ≤ radiusBound q s b := by
  unfold radiusBound
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  apply Nat.mul_le_mul_left
  omega

/-! ## The confusion graph -/

section Graph
variable {q : ℕ} (t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
include hq ht

theorem mem_scripts_iff (s : ℕ) (hs : 1 ≤ s) (x : Word q) (hx : 1 ≤ x.length) (y : Word q) :
    y ∈ (scripts s x).map Prod.snd ↔ distance x y ≤ s := by
  have := ((edit_ball_volume q s hq hs).1 x.length hx x rfl).2.1 y
  rw [← this]
  simp [ball]

theorem mem_confNbr (x : Word q) (hx : 1 ≤ x.length) (y : Word q) :
    y ∈ confusionNeighbors t x ↔ y.length = x.length ∧ y ≠ x ∧ distance x y ≤ 2 * t := by
  unfold confusionNeighbors
  rw [List.mem_eraseDups, List.mem_mergeSort, List.mem_filter,
    mem_scripts_iff t hq ht (2 * t) (by omega) x hx]
  simp only [decide_eq_true_eq]
  tauto

theorem confAdj {m : ℕ} (x u : FixedWord q m) :
    (confusionGraph q t m).Adj x u ↔ x ≠ u ∧ distance (toWord x) (toWord u) ≤ 2 * t := by
  unfold confusionGraph
  rw [SimpleGraph.fromRel_adj, dist_symm (toWord u)]
  tauto

theorem mem_confNbr_fixed {m : ℕ} (hm : 1 ≤ m) (x : FixedWord q m) (y : Word q) :
    y ∈ confusionNeighbors t (toWord x) ↔ ∃ u, (confusionGraph q t m).Adj x u ∧ toWord u = y := by
  rw [mem_confNbr t hq ht _ (by rw [length_toWord]; exact hm)]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [length_toWord] at h1
    refine ⟨ofWord y h1, ?_, toWord_ofWord y h1⟩
    rw [confAdj t hq ht, toWord_ofWord]
    refine ⟨fun h => h2 ?_, h3⟩
    rw [← toWord_ofWord y h1, ← h]
  · rintro ⟨u, hu, rfl⟩
    rw [confAdj t hq ht] at hu
    refine ⟨by simp [length_toWord], fun h => hu.1 (toWord_inj h).symm, hu.2⟩

theorem all_confNbr {m : ℕ} (hm : 1 ≤ m) (x : FixedWord q m) (Pr : Word q → Bool) :
    (confusionNeighbors t (toWord x)).all Pr = true ↔
      ∀ u, (confusionGraph q t m).Adj x u → Pr (toWord u) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h u hu
    exact h _ ((mem_confNbr_fixed t hq ht hm x _).2 ⟨u, hu, rfl⟩)
  · intro h y hy
    obtain ⟨u, hu, rfl⟩ := (mem_confNbr_fixed t hq ht hm x _).1 hy
    exact h u hu

theorem degree_le {m : ℕ} (hm : 1 ≤ m) (x : FixedWord q m) :
    (neighbors (confusionGraph q t m) x).card ≤ radiusBound q (2 * t) m := by
  classical
  have hball := ((edit_ball_volume q (2 * t) hq (by omega)).1 m hm (toWord x) (length_toWord x))
  refine le_trans ?_ hball.2.2
  rw [← Finset.card_image_of_injective _ toWord_inj]
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_image] at hy
  obtain ⟨u, hu, rfl⟩ := hy
  unfold neighbors at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rw [hball.2.1]
  exact ((confAdj t hq ht x u).1 hu).2

end Graph

/-! ## Parameters -/

theorem m_le_n (q t n : ℕ) : (parameters q t n).m ≤ n := by
  show n - shortLength q t _ ≤ n
  omega

theorem localColor_spec (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (hm : 1 ≤ (parameters q t n).m) (p : ℕ)
    (hp : ValidModulus (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) p)
    (x : FixedWord q (parameters q t n).m) :
    ∃ α < (parameters q t n).Q,
      localColor t (parameters q t n) p (toWord x) =
        (parameters q t n).Q * α +
          bitEval (parameters q t n).Q p (parameters q t n).K (value (toWord x)) α ∧
      ∀ u, (confusionGraph q t (parameters q t n).m).Adj x u →
        bitEval (parameters q t n).Q p (parameters q t n).K (value (toWord x)) α ≠
          bitEval (parameters q t n).Q p (parameters q t n).K (value (toWord u)) α := by
  have hQ : (parameters q t n).Q = fieldSize (parameters q t n).r (parameters q t n).K := rfl
  have hr : 1 ≤ (parameters q t n).r := by
    show 1 ≤ radiusBound q (2 * t) n
    unfold radiusBound
    have : 0 < 2 * q * (n + 2 * t + 1) := by positivity
    have := Nat.one_le_pow (2 * t) _ this
    nlinarith
  have hmn : (parameters q t n).m ≤ n := m_le_n q t n
  have hcl := le_two_pow_ceilLog q hq
  have hK : 1 ≤ (parameters q t n).K := by
    show 1 ≤ n * ceilLog 2 q
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hrange : ∀ v : FixedWord q (parameters q t n).m, value (toWord v) < 2 ^ (parameters q t n).K := by
    intro v
    refine lt_of_lt_of_le (value_ofFn_lt (by omega) v) ?_
    show q ^ (parameters q t n).m ≤ 2 ^ (n * ceilLog 2 q)
    calc q ^ (parameters q t n).m ≤ (2 ^ ceilLog 2 q) ^ (parameters q t n).m := Nat.pow_le_pow_left hcl.1 (parameters q t n).m
      _ = 2 ^ (ceilLog 2 q * (parameters q t n).m) := by rw [pow_mul]
      _ ≤ 2 ^ (n * ceilLog 2 q) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hdeg : ∀ v : FixedWord q (parameters q t n).m, (neighbors (confusionGraph q t (parameters q t n).m) v).card ≤ (parameters q t n).r :=
    fun v => le_trans (degree_le t hq ht hm v) (radiusBound_mono q (2 * t) hmn)
  obtain ⟨α0, hα0, hsep⟩ := bit_separating (confusionGraph q t (parameters q t n).m) (parameters q t n).r (parameters q t n).K hr hK hdeg
    (fun v => value (toWord v)) (fun u v h => value_ofFn_inj (by omega) u v h) hrange p hp x
  rw [← hQ] at hα0 hsep
  unfold localColor
  set pr : ℕ → Bool := fun a => (confusionNeighbors t (toWord x)).all fun y =>
    decide (bitEval (parameters q t n).Q p (parameters q t n).K (value (toWord x)) a ≠ bitEval (parameters q t n).Q p (parameters q t n).K (value y) a) with hpr
  have hprα : ∀ a, pr a = true ↔ ∀ u, (confusionGraph q t (parameters q t n).m).Adj x u →
      bitEval (parameters q t n).Q p (parameters q t n).K (value (toWord x)) a ≠ bitEval (parameters q t n).Q p (parameters q t n).K (value (toWord u)) a := by
    intro a
    rw [hpr]
    simp only
    rw [all_confNbr t hq ht hm x]
    simp
  cases hf : (List.range (parameters q t n).Q).find? pr with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd ((hprα α0).2 hsep) (hf α0 (List.mem_range.2 hα0))
  | some α =>
    refine ⟨α, List.mem_range.1 (List.mem_of_find?_eq_some hf), ?_, ?_⟩
    · show (parameters q t n).Q * ((List.find? pr (List.range (parameters q t n).Q)).getD 0) +
        bitEval (parameters q t n).Q p (parameters q t n).K (value (toWord x))
          ((List.find? pr (List.range (parameters q t n).Q)).getD 0) = _
      rw [hf]; rfl
    exact (hprα α).1 (List.find?_some hf)

end EditMulticoloring.Dev.Decoder
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Decoder
open EditMulticoloring.Code OAI.EditDistortion

/-! ## The vertex coloring is proper, with `B` bits -/

theorem Q_eq (q t n : ℕ) :
    (parameters q t n).Q = 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) := rfl

theorem B_eq (q t n : ℕ) :
    (parameters q t n).B = 2 * ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) := rfl

theorem localColor_facts (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (hm : 1 ≤ (parameters q t n).m) (p : ℕ)
    (hp : ValidModulus (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) p) :
    (∀ x : FixedWord q (parameters q t n).m,
      localColor t (parameters q t n) p (toWord x) < 2 ^ (parameters q t n).B) ∧
    (∀ x u : FixedWord q (parameters q t n).m, (confusionGraph q t (parameters q t n).m).Adj x u →
      localColor t (parameters q t n) p (toWord x) ≠ localColor t (parameters q t n) p (toWord u)) := by
  have hlt : ∀ (K id a : ℕ), bitEval (parameters q t n).Q p K id a < (parameters q t n).Q := by
    intro K id a
    rw [Q_eq]
    exact bitEval_lt hp K id a
  have hQ2 : 2 ^ (parameters q t n).B = (parameters q t n).Q * (parameters q t n).Q := by
    rw [B_eq, Q_eq, ← pow_add]; ring_nf
  refine ⟨fun x => ?_, fun x u hxu => ?_⟩
  · obtain ⟨α, hα, hc, -⟩ := localColor_spec q t n hq ht hm p hp x
    rw [hc, hQ2]
    have := hlt (parameters q t n).K (value (toWord x)) α
    nlinarith
  · obtain ⟨α, hα, hc, hs⟩ := localColor_spec q t n hq ht hm p hp x
    obtain ⟨β, hβ, hc', -⟩ := localColor_spec q t n hq ht hm p hp u
    rw [hc, hc']
    intro h
    have h1 := hlt (parameters q t n).K (value (toWord x)) α
    have h2 := hlt (parameters q t n).K (value (toWord u)) β
    have hQ : 0 < (parameters q t n).Q := by omega
    have e1 := congrArg (· / (parameters q t n).Q) h
    have e2 := congrArg (· % (parameters q t n).Q) h
    rw [Nat.mul_add_div hQ, Nat.mul_add_div hQ, Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2] at e1
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at e2
    have e1' : α = β := by omega
    subst e1'
    exact hs u hxu e2

theorem localGood_iff (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (hm : 1 ≤ (parameters q t n).m) (p : ℕ) (x : FixedWord q (parameters q t n).m) (i : ℕ) :
    localGood t (parameters q t n) p (toWord x) i = true ↔
      Good (confusionGraph q t (parameters q t n).m)
        (fun v => localColor t (parameters q t n) p (toWord v)) x i := by
  unfold localGood Good
  rw [all_confNbr t hq ht hm x]
  simp

theorem localGoodIndices_eq (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (hm : 1 ≤ (parameters q t n).m) (p : ℕ) (x : FixedWord q (parameters q t n).m) :
    localGoodIndices t (parameters q t n) p (toWord x) =
      goodIndices (confusionGraph q t (parameters q t n).m)
        (fun v => localColor t (parameters q t n) p (toWord v)) (parameters q t n).L x := by
  classical
  unfold localGoodIndices goodIndices
  apply List.filter_congr
  intro i _
  rw [Bool.eq_iff_iff, localGood_iff q t n hq ht hm p x i]
  simp

theorem multicolor (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (hm : 1 ≤ (parameters q t n).m) (p : ℕ)
    (hp : ValidModulus (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) p) :
    (∀ x : FixedWord q (parameters q t n).m,
      (parameters q t n).J ≤ (localGoodIndices t (parameters q t n) p (toWord x)).length) ∧
    (∀ x y : FixedWord q (parameters q t n).m, x ≠ y →
      distance (toWord x) (toWord y) ≤ 2 * t →
      ∀ j₁ < (parameters q t n).J, ∀ j₂ < (parameters q t n).J,
        localPair t (parameters q t n) p (toWord x) j₁ ≠
          localPair t (parameters q t n) p (toWord y) j₂) := by
  have hdeg : ∀ v : FixedWord q (parameters q t n).m,
      (neighbors (confusionGraph q t (parameters q t n).m) v).card ≤ (parameters q t n).r :=
    fun v => le_trans (degree_le t hq ht hm v) (radiusBound_mono q (2 * t) (m_le_n q t n))
  have hB : 1 ≤ (parameters q t n).B := by
    rw [B_eq]; have := hp.1; omega
  obtain ⟨hrange, hproper⟩ := localColor_facts q t n hq ht hm p hp
  have H := prime_multicoloring q hq (confusionGraph q t (parameters q t n).m)
    (parameters q t n).r (parameters q t n).B hB hdeg
    (fun v => localColor t (parameters q t n) p (toWord v)) hrange hproper
  obtain ⟨H1, -, H3⟩ := H
  have hL : paletteLength (parameters q t n).r (parameters q t n).B = (parameters q t n).L := rfl
  have hJ : foldCount q (parameters q t n).L = (parameters q t n).J := rfl
  rw [hL, hJ] at H1 H3
  have hpair : ∀ (x : FixedWord q (parameters q t n).m) j,
      localPair t (parameters q t n) p (toWord x) j =
        colorPair (confusionGraph q t (parameters q t n).m)
          (fun v => localColor t (parameters q t n) p (toWord v)) (parameters q t n).L x j := by
    intro x j
    unfold localPair colorPair
    rw [localGoodIndices_eq q t n hq ht hm p x]
  refine ⟨fun x => ?_, fun x y hxy hd j₁ hj₁ j₂ hj₂ h => ?_⟩
  · rw [localGoodIndices_eq q t n hq ht hm p x]; exact H1 x
  · have hadj : (confusionGraph q t (parameters q t n).m).Adj x y :=
      (confAdj t hq ht x y).2 ⟨hxy, hd⟩
    have := H3 x y hadj
    rw [hpair, hpair] at h
    have hm1 : colorPair (confusionGraph q t (parameters q t n).m)
        (fun v => localColor t (parameters q t n) p (toWord v)) (parameters q t n).L x j₁ ∈
        assigned (confusionGraph q t (parameters q t n).m)
        (fun v => localColor t (parameters q t n) p (toWord v)) (parameters q t n).L
        (parameters q t n).J x := by
      unfold assigned; simp only [List.mem_toFinset, List.mem_map, List.mem_range]
      exact ⟨j₁, hj₁, rfl⟩
    have hm2 : colorPair (confusionGraph q t (parameters q t n).m)
        (fun v => localColor t (parameters q t n) p (toWord v)) (parameters q t n).L y j₂ ∈
        assigned (confusionGraph q t (parameters q t n).m)
        (fun v => localColor t (parameters q t n) p (toWord v)) (parameters q t n).L
        (parameters q t n).J y := by
      unfold assigned; simp only [List.mem_toFinset, List.mem_map, List.mem_range]
      exact ⟨j₂, hj₂, rfl⟩
    rw [h] at hm1
    exact Finset.disjoint_left.1 this hm1 hm2

/-! ## Filtered index lists -/

theorem filter_range_split (g : ℕ → Bool) (L i : ℕ) (hi : i < L) (hg : g i = true) :
    ∃ B, (List.range L).filter g = (List.range i).filter g ++ i :: B := by
  obtain ⟨c, rfl⟩ : ∃ c, L = i + 1 + c := ⟨L - i - 1, by omega⟩
  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append]
  simp [hg]

theorem filter_range_get (g : ℕ → Bool) (L i : ℕ) (hi : i < L) (hg : g i = true) :
    ((List.range L).filter g)[((List.range i).filter g).length]? = some i := by
  obtain ⟨B, hB⟩ := filter_range_split g L i hi hg
  rw [hB]
  simp

theorem filter_range_count (g : ℕ → Bool) (L j : ℕ) (i : ℕ)
    (h : ((List.range L).filter g)[j]? = some i) :
    i < L ∧ g i = true ∧ ((List.range i).filter g).length = j := by
  have hmem : i ∈ (List.range L).filter g := List.mem_of_getElem? h
  rw [List.mem_filter, List.mem_range] at hmem
  refine ⟨hmem.1, hmem.2, ?_⟩
  have h2 := filter_range_get g L i hmem.1 hmem.2
  have hnd : ((List.range L).filter g).Nodup := (List.nodup_range).filter g
  obtain ⟨hj, hj'⟩ := List.getElem?_eq_some_iff.1 h
  obtain ⟨hk, hk'⟩ := List.getElem?_eq_some_iff.1 h2
  exact (hnd.getElem_inj_iff.1 (hk'.trans hj'.symm))

/-! ## `repr` and `value` -/

theorem repr_eq_map {q : ℕ} (hq : 0 < q) (w N : ℕ) :
    Code.repr q w N = (List.range w).map (fun i => (⟨(N / q ^ (w - 1 - i)) % q, Nat.mod_lt _ hq⟩ : Fin q)) := by
  unfold Code.repr
  rw [← List.filterMap_eq_map']
  apply List.filterMap_congr
  intro i _
  simp [Nat.mod_lt _ hq]

theorem repr_length {q : ℕ} (hq : 0 < q) (w N : ℕ) : (Code.repr q w N).length = w := by
  rw [repr_eq_map hq]; simp

theorem repr_succ {q : ℕ} (hq : 0 < q) (w N : ℕ) :
    Code.repr q (w + 1) N = Code.repr q w (N / q) ++ [⟨N % q, Nat.mod_lt _ hq⟩] := by
  rw [repr_eq_map hq, repr_eq_map hq, List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    congr 2
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
    congr 2
    omega
  · simp

theorem value_repr {q : ℕ} (hq : 0 < q) : ∀ (w N : ℕ), N < q ^ w → value (Code.repr q w N) = N := by
  intro w
  induction w with
  | zero => intro N hN; simp at hN; subst hN; simp [Code.repr, value]
  | succ w ih =>
    intro N hN
    rw [repr_succ hq, value_snoc, ih]
    · exact Nat.div_add_mod N q
    · rw [Nat.div_lt_iff_lt_mul hq]; rw [pow_succ] at hN; exact hN

theorem value_lt {q : ℕ} (hq : 0 < q) (x : Word q) : value x < q ^ x.length := by
  have := value_ofFn_lt hq (ofWord x rfl)
  rwa [show List.ofFn (ofWord x rfl) = x from toWord_ofWord x rfl] at this

theorem value_inj {q : ℕ} (hq : 0 < q) {x y : Word q} (hl : x.length = y.length)
    (h : value x = value y) : x = y := by
  have h' : value (toWord (ofWord x hl)) = value (toWord (ofWord y rfl)) := by
    rw [toWord_ofWord, toWord_ofWord]; exact h
  have := value_ofFn_inj hq _ _ h'
  calc x = toWord (ofWord x hl) := (toWord_ofWord x hl).symm
    _ = toWord (ofWord y rfl) := by rw [this]
    _ = y := toWord_ofWord y rfl

theorem repr_value {q : ℕ} (hq : 0 < q) (x : Word q) : Code.repr q x.length (value x) = x :=
  value_inj hq (repr_length hq _ _) (value_repr hq _ _ (value_lt hq x))

/-! ## Parameter arithmetic -/

theorem le_pow_ceilLog (q N : ℕ) (hq : 2 ≤ q) : N ≤ q ^ ceilLog q N := by
  unfold ceilLog floorLog
  dsimp only
  split_ifs with h
  · exact h
  · exact le_of_lt (Nat.lt_pow_succ_log_self (by omega) N)

theorem primeAt_mono {i j : ℕ} (h : i ≤ j) : primeAt i ≤ primeAt j :=
  Nat.nth_monotone Nat.infinite_setOfPred_prime h

theorem primeAt_pos (i : ℕ) : 0 < primeAt i := (Nat.prime_nth_prime i).pos

theorem J_eq (q t n : ℕ) (hq : 2 ≤ q) :
    (parameters q t n).k - (parameters q t n).m = floorLog q (parameters q t n).J ∧
    q ^ ((parameters q t n).k - (parameters q t n).m) = (parameters q t n).J ∧
    (parameters q t n).m ≤ (parameters q t n).k := by
  have hk : (parameters q t n).k = (parameters q t n).m + floorLog q (parameters q t n).J := rfl
  have hJ : (parameters q t n).J = q ^ floorLog q ((parameters q t n).L / 2) := rfl
  refine ⟨by omega, ?_, by omega⟩
  rw [show (parameters q t n).k - (parameters q t n).m = floorLog q (parameters q t n).J by omega]
  rw [hJ]
  unfold floorLog
  rw [Nat.log_pow (by omega)]

end EditMulticoloring.Dev.Decoder
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Decoder
open EditMulticoloring.Code OAI.EditDistortion

/-! ## The short code -/

theorem h_pos (q t n : ℕ) (hq : 2 ≤ q) : 1 ≤ (parameters q t n).h := by
  have hh : (parameters q t n).h = (parameters q t n).h₁ + (parameters q t n).h₂ := rfl
  have h2 : (parameters q t n).h₂ = ceilLog q (primeAt ((parameters q t n).L - 1)) := rfl
  have hle := le_pow_ceilLog q (primeAt ((parameters q t n).L - 1)) hq
  have hp2 := (Nat.prime_nth_prime ((parameters q t n).L - 1)).two_le
  rw [← h2] at hle
  rcases Nat.eq_zero_or_pos (parameters q t n).h₂ with h0 | h0
  · rw [h0] at hle; simp [primeAt] at hle; omega
  · omega

theorem short_facts (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    (shortTable q t (parameters q t n).h).length = q ^ (parameters q t n).h ∧
    (∀ s : Word q, s.length = (parameters q t n).h →
      (shortEncode t (parameters q t n).h s).length = (parameters q t n).ρ) ∧
    (∀ s₁ s₂ : Word q, s₁.length = (parameters q t n).h → s₂.length = (parameters q t n).h →
      shortEncode t (parameters q t n).h s₁ = shortEncode t (parameters q t n).h s₂ → s₁ = s₂) ∧
    (∀ s₁ s₂ : Word q, s₁.length = (parameters q t n).h → s₂.length = (parameters q t n).h →
      shortEncode t (parameters q t n).h s₁ ≠ shortEncode t (parameters q t n).h s₂ →
      ∀ y, ¬ (distance (shortEncode t (parameters q t n).h s₁) y ≤ t ∧
        distance (shortEncode t (parameters q t n).h s₂) y ≤ t)) ∧
    (q ^ (parameters q t n).h * radiusBound q (2 * t) (parameters q t n).ρ ≤
      q ^ (parameters q t n).ρ) := by
  obtain ⟨C, -, H⟩ := short_edit_code q t hq ht
  obtain ⟨-, ⟨-, hρ⟩, -, -, hT, hlen, hinj, hcor⟩ := H (parameters q t n).h (h_pos q t n hq)
  have hρ' : shortLength q t (parameters q t n).h = (parameters q t n).ρ := rfl
  rw [hρ'] at hρ hlen
  refine ⟨hT, fun s hs => ?_, fun s₁ s₂ h1 h2 he => ?_, fun s₁ s₂ h1 h2 hne y hy => ?_, hρ⟩
  · have := hlen (ofWord s hs); rwa [toWord_ofWord] at this
  · have := @hinj (ofWord s₁ h1) (ofWord s₂ h2) (by simp only [toWord_ofWord]; exact he)
    rw [← toWord_ofWord s₁ h1, ← toWord_ofWord s₂ h2, this]
  · refine hcor _ ⟨ofWord s₁ h1, rfl⟩ _ ⟨ofWord s₂ h2, rfl⟩ ?_ y ?_
    · simp only [toWord_ofWord]; exact hne
    · simp only [toWord_ofWord]; exact hy

theorem shortEncode_eq (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (s : Word q)
    (hs : s.length = (parameters q t n).h) :
    ∃ hv : value s < (shortTable q t (parameters q t n).h).length,
      shortEncode t (parameters q t n).h s = (shortTable q t (parameters q t n).h)[value s] := by
  have hT := (short_facts q t n hq ht).1
  have hv : value s < (shortTable q t (parameters q t n).h).length := by
    rw [hT, ← hs]; exact value_lt (by omega) s
  refine ⟨hv, ?_⟩
  unfold shortEncode
  rw [List.getElem?_eq_getElem hv]
  rfl

theorem shortTable_nodup (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    (shortTable q t (parameters q t n).h).Nodup := by
  obtain ⟨hT, -, hinj, -⟩ := short_facts q t n hq ht
  have hq0 : 0 < q := by omega
  rw [List.nodup_iff_injective_get]
  intro a b hab
  have ha : a.val < q ^ (parameters q t n).h := hT ▸ a.isLt
  have hb : b.val < q ^ (parameters q t n).h := hT ▸ b.isLt
  have hra := repr_length hq0 (parameters q t n).h a.val
  have hrb := repr_length hq0 (parameters q t n).h b.val
  obtain ⟨_, ea⟩ := shortEncode_eq q t n hq ht _ hra
  obtain ⟨_, eb⟩ := shortEncode_eq q t n hq ht _ hrb
  simp only [value_repr hq0 _ _ ha, value_repr hq0 _ _ hb] at ea eb
  have := hinj _ _ hra hrb (by rw [ea, eb]; exact hab)
  apply Fin.ext
  rw [← value_repr hq0 _ _ ha, ← value_repr hq0 _ _ hb, this]

theorem shortInverse_eq (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (s : Word q)
    (hs : s.length = (parameters q t n).h) :
    shortInverse t (parameters q t n).h (shortEncode t (parameters q t n).h s) = some s := by
  obtain ⟨hv, he⟩ := shortEncode_eq q t n hq ht s hs
  unfold shortInverse
  dsimp only
  rw [he, if_pos (List.getElem_mem hv), (shortTable_nodup q t n hq ht).idxOf_getElem, ← hs,
    repr_value (by omega)]

theorem shortInverse_some (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (z s : Word q)
    (h : shortInverse t (parameters q t n).h z = some s) :
    s.length = (parameters q t n).h ∧ shortEncode t (parameters q t n).h s = z := by
  unfold shortInverse at h
  dsimp only at h
  split_ifs at h with hz
  injection h with h
  subst h
  have hT := (short_facts q t n hq ht).1
  have hi := List.idxOf_lt_length_of_mem hz
  have hlen := repr_length (by omega : 0 < q) (parameters q t n).h
    ((shortTable q t (parameters q t n).h).idxOf z)
  refine ⟨hlen, ?_⟩
  obtain ⟨hv, he⟩ := shortEncode_eq q t n hq ht _ hlen
  simp only [he]
  have : value (Code.repr q (parameters q t n).h ((shortTable q t (parameters q t n).h).idxOf z)) =
      (shortTable q t (parameters q t n).h).idxOf z :=
    value_repr (by omega) _ _ (by rw [← hT]; exact hi)
  simp only [this]
  exact List.getElem_idxOf hi

/-! ## Parameter facts -/

theorem rho_gt (q t n : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) : t < (parameters q t n).ρ := by
  have H := (short_facts q t n hq ht).2.2.2.2
  by_contra hle
  push Not at hle
  set ρ := (parameters q t n).ρ
  have h1 : 2 ≤ q ^ (parameters q t n).h :=
    le_trans hq (Nat.le_self_pow (by have := h_pos q t n hq; omega) q)
  have h2 : q ^ ρ ≤ radiusBound q (2 * t) ρ := by
    unfold radiusBound
    calc q ^ ρ ≤ q ^ (2 * t) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ (2 * q * (ρ + 2 * t + 1)) ^ (2 * t) := Nat.pow_le_pow_left (by nlinarith) _
      _ ≤ (2 * t + 1) * (2 * q * (ρ + 2 * t + 1)) ^ (2 * t) := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : 0 < q ^ ρ := by positivity
  nlinarith

theorem n_eq (q t n : ℕ) (hm : 1 ≤ (parameters q t n).m) :
    n = (parameters q t n).m + (parameters q t n).ρ := by
  have : (parameters q t n).m = n - (parameters q t n).ρ := rfl
  omega

theorem bounds_h (q t n : ℕ) (hq : 2 ≤ q) :
    (parameters q t n).L ≤ q ^ (parameters q t n).h₁ ∧
    primeAt ((parameters q t n).L - 1) ≤ q ^ (parameters q t n).h₂ ∧
    (parameters q t n).h = (parameters q t n).h₁ + (parameters q t n).h₂ :=
  ⟨le_pow_ceilLog q _ hq, le_pow_ceilLog q _ hq, rfl⟩

theorem serialize_eq (q : ℕ) (P : Parameters) (c : ℕ × ℕ) :
    serialize q P c = Code.repr q P.h₁ c.1 ++ Code.repr q P.h₂ c.2 := rfl

end EditMulticoloring.Dev.Decoder
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Decoder
open EditMulticoloring.Code OAI.EditDistortion

section
variable (q t n p : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (hm : 1 ≤ (parameters q t n).m)
  (hp : ValidModulus (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) p)
include hq ht hm hp

/-- The pair attached to a good-index rank `j < J`, and its serialization. -/
theorem pair_facts (x : Word q) (hx : x.length = (parameters q t n).m) (j : ℕ)
    (hj : j < (parameters q t n).J) :
    ∃ i, (localGoodIndices t (parameters q t n) p x)[j]? = some i ∧ i < (parameters q t n).L ∧
      localGood t (parameters q t n) p x i = true ∧
      ((List.range i).filter (localGood t (parameters q t n) p x)).length = j ∧
      localPair t (parameters q t n) p x j =
        (i, localColor t (parameters q t n) p x % primeAt i) ∧
      (serialize q (parameters q t n) (localPair t (parameters q t n) p x j)).length =
        (parameters q t n).h ∧
      value ((serialize q (parameters q t n) (localPair t (parameters q t n) p x j)).take
        (parameters q t n).h₁) = i ∧
      value ((serialize q (parameters q t n) (localPair t (parameters q t n) p x j)).drop
        (parameters q t n).h₁) = localColor t (parameters q t n) p x % primeAt i := by
  have hq0 : 0 < q := by omega
  have hgood := (multicolor q t n hq ht hm p hp).1 (ofWord x hx)
  rw [toWord_ofWord] at hgood
  have hjl : j < (localGoodIndices t (parameters q t n) p x).length := by omega
  obtain ⟨i, hi⟩ : ∃ i, (localGoodIndices t (parameters q t n) p x)[j]? = some i :=
    ⟨_, List.getElem?_eq_getElem hjl⟩
  obtain ⟨hiL, hig, hcnt⟩ := filter_range_count _ _ j i hi
  have hpair : localPair t (parameters q t n) p x j =
      (i, localColor t (parameters q t n) p x % primeAt i) := by
    unfold localPair; rw [hi]; rfl
  obtain ⟨hL1, hL2, hh⟩ := bounds_h q t n hq
  have hη : localColor t (parameters q t n) p x % primeAt i < q ^ (parameters q t n).h₂ :=
    lt_of_lt_of_le (Nat.mod_lt _ (primeAt_pos i)) (le_trans (primeAt_mono (by omega)) hL2)
  have hl1 := repr_length hq0 (parameters q t n).h₁ i
  refine ⟨i, hi, hiL, hig, hcnt, hpair, ?_, ?_, ?_⟩
  · rw [hpair, serialize_eq, List.length_append, repr_length hq0, repr_length hq0, hh]
  · rw [hpair, serialize_eq, List.take_left' hl1]
    exact value_repr hq0 _ _ (by omega)
  · rw [hpair, serialize_eq, List.drop_left' hl1]
    exact value_repr hq0 _ _ hη

theorem encode_length (u : Word q) (hu : u.length = (parameters q t n).k) :
    (encode t n p u).length = n := by
  have hq0 : 0 < q := by omega
  obtain ⟨-, hJ, hmk⟩ := J_eq q t n hq
  have hx : (u.take (parameters q t n).m).length = (parameters q t n).m := by
    rw [List.length_take]; omega
  have hj : value (u.drop (parameters q t n).m) < (parameters q t n).J := by
    rw [← hJ]; have := value_lt hq0 (u.drop (parameters q t n).m)
    rwa [List.length_drop, hu] at this
  obtain ⟨i, -, -, -, -, -, hsl, -, -⟩ := pair_facts q t n p hq ht hm hp _ hx _ hj
  have hz := (short_facts q t n hq ht).2.1 _ hsl
  unfold encode
  dsimp only
  rw [List.length_append, hx, hz, ← n_eq q t n hm]

theorem validate_encode (u : Word q) (hu : u.length = (parameters q t n).k) :
    validate t n p (encode t n p u) = some u := by
  have hq0 : 0 < q := by omega
  have hlenc := encode_length q t n p hq ht hm hp u hu
  obtain ⟨-, hJ, hmk⟩ := J_eq q t n hq
  have hx : (u.take (parameters q t n).m).length = (parameters q t n).m := by
    rw [List.length_take]; omega
  have hj : value (u.drop (parameters q t n).m) < (parameters q t n).J := by
    rw [← hJ]; have := value_lt hq0 (u.drop (parameters q t n).m)
    rwa [List.length_drop, hu] at this
  obtain ⟨i, -, hiL, hig, hcnt, hpair, hsl, hv1, hv2⟩ := pair_facts q t n p hq ht hm hp _ hx _ hj
  have hinv := shortInverse_eq q t n hq ht _ hsl
  unfold encode at hlenc ⊢
  dsimp only at hlenc ⊢
  unfold validate
  dsimp only
  rw [if_neg (by rw [hlenc]; exact fun h => h rfl), List.take_left' hx, List.drop_left' hx, hinv]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hv1, hv2, hcnt]
  rw [if_neg (by
    push Not
    exact ⟨hiL, Nat.mod_lt _ (primeAt_pos i)⟩)]
  rw [if_neg (by simp [hig]), if_neg (by omega)]
  congr 1
  conv_rhs => rw [← List.take_append_drop (parameters q t n).m u]
  congr 1
  have hdl : (u.drop (parameters q t n).m).length = (parameters q t n).k - (parameters q t n).m := by
    rw [List.length_drop, hu]
  rw [← hdl, repr_value hq0]

theorem encode_validate (c w : Word q) (h : validate t n p c = some w) :
    w.length = (parameters q t n).k ∧ encode t n p w = c := by
  have hq0 : 0 < q := by omega
  obtain ⟨-, hJ, hmk⟩ := J_eq q t n hq
  have hnm := n_eq q t n hm
  unfold validate at h
  dsimp only at h
  split_ifs at h with hlen
  push Not at hlen
  cases hs : shortInverse t (parameters q t n).h (c.drop (parameters q t n).m) with
  | none => rw [hs] at h; simp at h
  | some s =>
    rw [hs] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨hsl, hse⟩ := shortInverse_some q t n hq ht _ s hs
    split_ifs at h with h1 h2 h3
    injection h with h
    subst h
    push Not at h1 h2 h3
    have h2g : localGood t (parameters q t n) p (c.take (parameters q t n).m)
        (value (s.take (parameters q t n).h₁)) = true := by simpa using h2.1
    have hx : (c.take (parameters q t n).m).length = (parameters q t n).m := by
      rw [List.length_take]; omega
    set x := c.take (parameters q t n).m with hxdef
    set i := value (s.take (parameters q t n).h₁) with hidef
    set j := ((List.range i).filter (localGood t (parameters q t n) p x)).length with hjdef
    have hrl := repr_length hq0 ((parameters q t n).k - (parameters q t n).m) j
    refine ⟨by rw [List.length_append, hx, hrl]; omega, ?_⟩
    obtain ⟨i', hi', -, -, -, hpair, -, -, -⟩ := pair_facts q t n p hq ht hm hp x hx j h3
    have hget := filter_range_get (localGood t (parameters q t n) p x) (parameters q t n).L i
      h1.1 h2g
    rw [← hjdef] at hget
    have hii : i' = i := by
      have : (localGoodIndices t (parameters q t n) p x)[j]? = some i := hget
      rw [hi'] at this; injection this
    subst hii
    unfold encode
    dsimp only
    rw [List.take_left' hx, List.drop_left' hx, value_repr hq0 _ _ (by rw [hJ]; exact h3), hpair,
      serialize_eq]
    dsimp only
    obtain ⟨-, -, hh⟩ := bounds_h q t n hq
    have hs1 : (s.take (parameters q t n).h₁).length = (parameters q t n).h₁ := by
      rw [List.length_take]; omega
    have hs2 : (s.drop (parameters q t n).h₁).length = (parameters q t n).h₂ := by
      rw [List.length_drop]; omega
    have e1 : Code.repr q (parameters q t n).h₁ i = s.take (parameters q t n).h₁ := by
      have := repr_value hq0 (s.take (parameters q t n).h₁)
      rw [hs1] at this; exact this
    have e2 : Code.repr q (parameters q t n).h₂ (localColor t (parameters q t n) p x % primeAt i) =
        s.drop (parameters q t n).h₁ := by
      have := repr_value hq0 (s.drop (parameters q t n).h₁)
      rw [hs2] at this; rw [← h2.2]; exact this
    rw [e1, e2, List.take_append_drop, hse, List.take_append_drop]

end

end EditMulticoloring.Dev.Decoder
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Decoder
open EditMulticoloring.Code OAI.EditDistortion

section
variable (q t n p : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (hm : 1 ≤ (parameters q t n).m)
  (hp : ValidModulus (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) p)
include hq ht hm hp

/-- Two distinct messages never have codewords within distance `t` of a common word. -/
theorem code_separated (u₁ u₂ : Word q) (h₁ : u₁.length = (parameters q t n).k)
    (h₂ : u₂.length = (parameters q t n).k) (hne : u₁ ≠ u₂) (y : Word q)
    (d₁ : distance y (encode t n p u₁) ≤ t) (d₂ : distance y (encode t n p u₂) ≤ t) : False := by
  have hq0 : 0 < q := by omega
  obtain ⟨-, hJ, hmk⟩ := J_eq q t n hq
  have hnm := n_eq q t n hm
  have hρt := rho_gt q t n hq ht
  have hd : distance (encode t n p u₁) (encode t n p u₂) ≤ 2 * t := by
    have := dist_triangle (encode t n p u₁) y (encode t n p u₂)
    rw [dist_symm (encode t n p u₁) y] at this
    omega
  have hl₁ := encode_length q t n p hq ht hm hp u₁ h₁
  have hl₂ := encode_length q t n p hq ht hm hp u₂ h₂
  -- structure of the codewords
  have hx₁ : (u₁.take (parameters q t n).m).length = (parameters q t n).m := by
    rw [List.length_take]; omega
  have hx₂ : (u₂.take (parameters q t n).m).length = (parameters q t n).m := by
    rw [List.length_take]; omega
  have hj₁ : value (u₁.drop (parameters q t n).m) < (parameters q t n).J := by
    rw [← hJ]; have := value_lt hq0 (u₁.drop (parameters q t n).m)
    rwa [List.length_drop, h₁] at this
  have hj₂ : value (u₂.drop (parameters q t n).m) < (parameters q t n).J := by
    rw [← hJ]; have := value_lt hq0 (u₂.drop (parameters q t n).m)
    rwa [List.length_drop, h₂] at this
  obtain ⟨i₁, hg₁, -, -, hc₁, hp₁, hs₁, hv₁, hw₁⟩ := pair_facts q t n p hq ht hm hp _ hx₁ _ hj₁
  obtain ⟨i₂, hg₂, -, -, hc₂, hp₂, hs₂, hv₂, hw₂⟩ := pair_facts q t n p hq ht hm hp _ hx₂ _ hj₂
  set x₁ := u₁.take (parameters q t n).m
  set x₂ := u₂.take (parameters q t n).m
  set s₁ := serialize q (parameters q t n)
    (localPair t (parameters q t n) p x₁ (value (u₁.drop (parameters q t n).m)))
  set s₂ := serialize q (parameters q t n)
    (localPair t (parameters q t n) p x₂ (value (u₂.drop (parameters q t n).m)))
  have he₁ : encode t n p u₁ = x₁ ++ shortEncode t (parameters q t n).h s₁ := rfl
  have he₂ : encode t n p u₂ = x₂ ++ shortEncode t (parameters q t n).h s₂ := rfl
  have hz₁ := (short_facts q t n hq ht).2.1 _ hs₁
  have hz₂ := (short_facts q t n hq ht).2.1 _ hs₂
  -- restriction to the two intervals
  have hsuf : ∀ (x z : Word q), x.length = (parameters q t n).m →
      interval (x ++ z) ((parameters q t n).m + 1) n = z.take (n - (parameters q t n).m) := by
    intro x z hx
    unfold interval
    rw [Nat.add_sub_cancel, List.drop_left' hx]
    congr 1; omega
  have hpre : ∀ (x z : Word q), x.length = (parameters q t n).m →
      interval (x ++ z) 1 (parameters q t n).m = x := by
    intro x z hx
    unfold interval
    rw [Nat.sub_self, List.drop_zero, Nat.sub_add_cancel hm, List.take_left' hx]
  have hdz := interval_restriction q t hq ht n ((parameters q t n).m + 1) n (by omega) (by omega)
    le_rfl _ _ hl₁ hl₂
  rw [he₁, he₂, hsuf _ _ hx₁, hsuf _ _ hx₂, List.take_of_length_le (by omega),
    List.take_of_length_le (by omega), ← he₁, ← he₂] at hdz
  by_cases hzz : shortEncode t (parameters q t n).h s₁ = shortEncode t (parameters q t n).h s₂
  · have hss := (short_facts q t n hq ht).2.2.1 _ _ hs₁ hs₂ hzz
    have hi : i₁ = i₂ := by rw [← hv₁, ← hv₂, hss]
    subst hi
    have hη : localColor t (parameters q t n) p x₁ % primeAt i₁ =
        localColor t (parameters q t n) p x₂ % primeAt i₁ := by rw [← hw₁, ← hw₂, hss]
    by_cases hxx : x₁ = x₂
    · -- equal prefixes: the ranks agree, hence the messages agree
      have hjj : value (u₁.drop (parameters q t n).m) = value (u₂.drop (parameters q t n).m) := by
        rw [← hc₁, ← hc₂, hxx]
      apply hne
      have hdd := value_inj hq0 (by rw [List.length_drop, List.length_drop, h₁, h₂]) hjj
      rw [← List.take_append_drop (parameters q t n).m u₁,
        ← List.take_append_drop (parameters q t n).m u₂]
      exact congrArg₂ (· ++ ·) hxx hdd
    · -- distinct prefixes: adjacent in the confusion graph, disjoint color sets
      have hdx := interval_restriction q t hq ht n 1 (parameters q t n).m le_rfl hm
        (m_le_n q t n) _ _ hl₁ hl₂
      rw [he₁, he₂, hpre _ _ hx₁, hpre _ _ hx₂, ← he₁, ← he₂] at hdx
      have hne' : ofWord x₁ hx₁ ≠ ofWord x₂ hx₂ := by
        intro h; apply hxx
        rw [← toWord_ofWord x₁ hx₁, ← toWord_ofWord x₂ hx₂, h]
      have := (multicolor q t n hq ht hm p hp).2 (ofWord x₁ hx₁) (ofWord x₂ hx₂) hne'
        (by rw [toWord_ofWord, toWord_ofWord]; omega) _ hj₁ _ hj₂
      rw [toWord_ofWord, toWord_ofWord, hp₁, hp₂, hη] at this
      exact this rfl
  · obtain ⟨w, hw₁', hw₂'⟩ := midpoint t _ _ (le_trans hdz hd)
    rw [dist_symm] at hw₂'
    exact (short_facts q t n hq ht).2.2.2.1 _ _ hs₁ hs₂ hzz w ⟨hw₁', hw₂'⟩

theorem decode_some (y w : Word q) (h : decode t n p y = some w) :
    w.length = (parameters q t n).k ∧ distance y (encode t n p w) ≤ t := by
  have hnm := n_eq q t n hm
  have hρt := rho_gt q t n hq ht
  unfold decode at h
  dsimp only at h
  split_ifs at h with hc
  push Not at hc
  have hyl : y.length ≤ n + t := by
    by_contra hh; push Not at hh
    rw [List.length_take] at hc; omega
  rw [List.take_of_length_le (by omega)] at h hc
  obtain ⟨c, hcmem, hv⟩ := List.exists_of_findSome?_eq_some h
  rw [mem_scripts_iff t hq ht t ht y (by omega)] at hcmem
  obtain ⟨hwl, hwe⟩ := encode_validate q t n p hq ht hm hp c w hv
  exact ⟨hwl, hwe ▸ hcmem⟩

theorem decode_ne_none (u y : Word q) (hu : u.length = (parameters q t n).k)
    (hd : distance y (encode t n p u) ≤ t) : decode t n p y ≠ none := by
  have hnm := n_eq q t n hm
  have hρt := rho_gt q t n hq ht
  have hl := encode_length q t n p hq ht hm hp u hu
  have hdl := dist_length y (encode t n p u)
  rw [hl] at hdl
  unfold decode
  dsimp only
  rw [List.take_of_length_le (by omega), if_neg (by omega)]
  intro h
  rw [List.findSome?_eq_none_iff] at h
  have hmem : encode t n p u ∈ (scripts t y).map Prod.snd :=
    (mem_scripts_iff t hq ht t ht y (by omega) _).2 hd
  have := h _ hmem
  rw [validate_encode q t n p hq ht hm hp u hu] at this
  exact Option.some_ne_none _ this

end

end EditMulticoloring.Dev.Decoder

namespace EditMulticoloring.Code

open EditMulticoloring.Dev.Decoder in
theorem chk_decoder_correctness (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (n : ℕ) (hm : 1 ≤ (parameters q t n).m)
    (p : ℕ) (hp : ValidModulus
      (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) p) :
    (∀ (u : FixedWord q (parameters q t n).k) (y : Word q),
      decode t n p y = some (toWord u) ↔ distance y (encode t n p (toWord u)) ≤ t) ∧
    (∀ y : Word q, decode t n p y = none ↔
      ∀ u : FixedWord q (parameters q t n).k, t < distance y (encode t n p (toWord u))) := by
  refine ⟨fun u y => ⟨fun h => (decode_some q t n p hq ht hm hp y _ h).2, fun hd => ?_⟩,
    fun y => ⟨fun h u => ?_, fun h => ?_⟩⟩
  · have hu := length_toWord u
    cases hdec : decode t n p y with
    | none => exact absurd hdec (decode_ne_none q t n p hq ht hm hp _ y hu hd)
    | some w =>
      obtain ⟨hwl, hwd⟩ := decode_some q t n p hq ht hm hp y w hdec
      by_contra hne
      exact code_separated q t n p hq ht hm hp w (toWord u) hwl hu
        (fun h => hne (by rw [h])) y hwd hd
  · by_contra hle
    push Not at hle
    exact decode_ne_none q t n p hq ht hm hp _ y (length_toWord u) hle h
  · cases hdec : decode t n p y with
    | none => rfl
    | some w =>
      obtain ⟨hwl, hwd⟩ := decode_some q t n p hq ht hm hp y w hdec
      have := h (ofWord w hwl)
      rw [toWord_ofWord] at this
      omega

end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_decoder_correctness := @EditMulticoloring.Code.chk_decoder_correctness
