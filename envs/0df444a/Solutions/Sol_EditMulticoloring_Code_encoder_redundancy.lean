-- Prove2me | solution 1 for EditMulticoloring.Code.encoder_redundancy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:58.697064+00:00
-- url     : https://prove2.me/submissions/9bb3f567-b811-493f-8005-6814909399e2

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Theorems.Thm_EditMulticoloring_Code_polynomial_coloring
import Theorems.Thm_EditMulticoloring_Code_edit_ball_volume
import Theorems.Thm_EditMulticoloring_Code_prime_multicoloring
import Theorems.Thm_EditMulticoloring_Code_short_edit_code

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

/-! ## Parameter facts -/

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

end

end EditMulticoloring.Dev.Decoder
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Redundancy

theorem two_mul_add_one_le_two_pow : ∀ s : ℕ, 3 ≤ s → 2 * s + 1 ≤ 2 ^ s
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, _ => by norm_num
  | s + 4, _ => by
    have := two_mul_add_one_le_two_pow (s + 3) (by omega)
    rw [pow_succ]; omega

/-- A Chebyshev-type upper bound on the `N`-th prime (zero based), from Mathlib's
`Chebyshev.pi_ge`. -/
theorem nth_prime_le (N : ℕ) :
    Nat.nth Nat.Prime N ≤ (N + 2) * (2 * (Nat.log 2 (N + 2) + 3)) := by
  set s := Nat.log 2 (N + 2) + 3 with hs
  set x := (N + 2) * (2 * s) with hx
  have h1 : N + 2 < 2 ^ s := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N + 2)
    calc N + 2 < 2 ^ (Nat.log 2 (N + 2) + 1) := this
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := two_mul_add_one_le_two_pow s (by omega)
  have h3 : x + 1 ≤ 2 ^ (2 * s) := by
    have : (N + 2) * (2 * s + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul h1.le h2
    rw [two_mul s, pow_add]
    have : (N + 2) * (2 * s + 1) = x + (N + 2) := by rw [hx]; ring
    omega
  have hx12 : 12 ≤ x := by
    have : 6 ≤ 2 * s := by omega
    calc 12 = 2 * 6 := by norm_num
      _ ≤ (N + 2) * (2 * s) := Nat.mul_le_mul (by omega) this
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlx1 : Real.log (x : ℝ) ≤ Real.log ((x : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have h4 : Real.log ((x : ℝ) + 1) ≤ (2 * s : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h3
  have h5 : ((N : ℝ) + 1) ≤ ((x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1)) / Real.log x := by
    rw [le_div_iff₀ hlx]
    have hxr : (x : ℝ) = ((N : ℝ) + 2) * ((2 * s : ℕ) : ℝ) := by rw [hx]; push_cast; ring
    have : ((N : ℝ) + 2) * Real.log ((x : ℝ) + 1) ≤ (x : ℝ) * Real.log 2 := by
      calc ((N : ℝ) + 2) * Real.log ((x : ℝ) + 1)
          ≤ ((N : ℝ) + 2) * (((2 * s : ℕ) : ℝ) * Real.log 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (x : ℝ) * Real.log 2 := by rw [hxr]; ring
    nlinarith
  have h6 := Chebyshev.pi_ge x
  have h7 : N < Nat.primeCounting x := by
    have : (N : ℝ) < (Nat.primeCounting x : ℝ) := by linarith
    exact_mod_cast this
  have h8 : Nat.nth Nat.Prime N < x + 1 := by
    apply Nat.nth_lt_of_lt_count
    rw [← Nat.primeCounting', ← Nat.primeCounting_eq_primeCounting'_succ] at *
    exact h7
  omega

end EditMulticoloring.Dev.Redundancy
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Redundancy
open EditMulticoloring.Code

/-! ## Words -/

theorem mem_words {q n : ℕ} (w : Word q) : w ∈ words q n ↔ w.length = n := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words, ih]

theorem words_length (q n : ℕ) : (words q n).length = q ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    simp [words, List.length_flatMap, ih, pow_succ, mul_comm]

theorem words_nodup (q n : ℕ) : (words q n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    unfold words
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => ih.map (fun x y h => by simpa using h), ?_⟩
    refine (List.nodup_finRange q).imp ?_
    intro a b hab
    rw [Function.onFun, List.disjoint_left]
    intro w hw hw'
    simp only [List.mem_map] at hw hw'
    obtain ⟨x, _, rfl⟩ := hw
    obtain ⟨y, _, hy⟩ := hw'
    exact hab (List.cons.inj hy).1.symm

/-! ## Real logarithms of the integer logarithms -/

theorem floorLog_mul_log_le (q X : ℕ) (hq : 2 ≤ q) (hX : 1 ≤ X) :
    (floorLog q X : ℝ) * Real.log q ≤ Real.log X := by
  have h := Nat.pow_log_le_self q (by omega : X ≠ 0)
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast h)

theorem log_lt_floorLog_succ (q X : ℕ) (hq : 2 ≤ q) (hX : 1 ≤ X) :
    Real.log X < ((floorLog q X : ℝ) + 1) * Real.log q := by
  have h := Nat.lt_pow_succ_log_self (by omega : 1 < q) X
  have : ((floorLog q X : ℝ) + 1) * Real.log q = Real.log ((q : ℝ) ^ (floorLog q X + 1)) := by
    rw [Real.log_pow]; push_cast; ring
  rw [this]
  exact Real.log_lt_log (by exact_mod_cast hX) (by exact_mod_cast h)

theorem ceilLog_le_succ (q X : ℕ) : ceilLog q X ≤ floorLog q X + 1 := by
  unfold ceilLog; dsimp only; split_ifs <;> omega

theorem floorLog_le_ceilLog (q X : ℕ) : floorLog q X ≤ ceilLog q X := by
  unfold ceilLog; dsimp only; split_ifs <;> omega

theorem ceilLog_mul_log_le (q X : ℕ) (hq : 2 ≤ q) (hX : 1 ≤ X) :
    (ceilLog q X : ℝ) * Real.log q ≤ Real.log X + Real.log q := by
  have h1 := floorLog_mul_log_le q X hq hX
  have h2 : (ceilLog q X : ℝ) ≤ (floorLog q X : ℝ) + 1 := by exact_mod_cast ceilLog_le_succ q X
  have hl : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  nlinarith

theorem log_le_ceilLog_mul (q X : ℕ) (hq : 2 ≤ q) (hX : 1 ≤ X) :
    Real.log X ≤ (ceilLog q X : ℝ) * Real.log q := by
  have h : X ≤ q ^ ceilLog q X := by
    unfold ceilLog floorLog
    dsimp only
    split_ifs with h
    · exact h
    · exact le_of_lt (Nat.lt_pow_succ_log_self (by omega) X)
  rw [← Real.log_pow]
  exact Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast h)

/-! ## Elementary facts about `log n` -/

theorem one_le_log {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact le_trans h3.le (by exact_mod_cast hn)

theorem loglog_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ Real.log (Real.log n) :=
  Real.log_nonneg (one_le_log hn)

theorem loglog_le_log {n : ℕ} (hn : 3 ≤ n) : Real.log (Real.log n) ≤ Real.log n := by
  have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos (one_le_log hn))
  linarith

theorem one_le_loglog {n : ℕ} (hn : 27 ≤ n) : 1 ≤ Real.log (Real.log n) := by
  have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact h3
  have : Real.exp 1 ≤ Real.log n := by
    have h27 : Real.log 27 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have : Real.log (27 : ℝ) = 3 * Real.log 3 := by
      rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]
  exact this

theorem log_lt_two_sqrt {n : ℕ} (hn : 1 ≤ n) : Real.log n < 2 * Real.sqrt n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h := Real.log_le_sub_one_of_pos hs
  have : Real.log (Real.sqrt n) = Real.log n / 2 := Real.log_sqrt (by positivity)
  linarith

theorem eventually_lt (c : ℝ) (hc : 0 ≤ c) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * Real.log n < n := by
  refine ⟨⌈(2 * c + 1) ^ 2⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnr : (2 * c + 1) ^ 2 ≤ (n : ℝ) := by
    have := Nat.le_ceil ((2 * c + 1) ^ 2)
    have : ((⌈(2 * c + 1) ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈(2 * c + 1) ^ 2⌉₊ ≤ n)
    linarith
  have hs : 2 * c + 1 ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hnr
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
  have hl := log_lt_two_sqrt hn1
  have hspos : 0 < Real.sqrt n := by linarith
  have : c * Real.log n ≤ c * (2 * Real.sqrt n) := mul_le_mul_of_nonneg_left hl.le hc
  nlinarith

end EditMulticoloring.Dev.Redundancy
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Redundancy
open EditMulticoloring.Code

/-! ## Size of the parameters -/

section
variable (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
include hq ht

theorem r_ge (n : ℕ) : n ^ (2 * t) ≤ (parameters q t n).r := by
  show n ^ (2 * t) ≤ (2 * t + 1) * (2 * q * (n + 2 * t + 1)) ^ (2 * t)
  calc n ^ (2 * t) ≤ (2 * q * (n + 2 * t + 1)) ^ (2 * t) :=
        Nat.pow_le_pow_left (by nlinarith) _
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)

theorem r_le (n : ℕ) (hn : 1 ≤ n) :
    (parameters q t n).r ≤ ((2 * t + 1) * (2 * q * (2 * t + 2)) ^ (2 * t)) * n ^ (2 * t) := by
  show (2 * t + 1) * (2 * q * (n + 2 * t + 1)) ^ (2 * t) ≤ _
  have : n + 2 * t + 1 ≤ (2 * t + 2) * n := by nlinarith
  have h2 : 2 * q * (n + 2 * t + 1) ≤ 2 * q * (2 * t + 2) * n := by
    calc 2 * q * (n + 2 * t + 1) ≤ 2 * q * ((2 * t + 2) * n) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  calc (2 * t + 1) * (2 * q * (n + 2 * t + 1)) ^ (2 * t)
      ≤ (2 * t + 1) * (2 * q * (2 * t + 2) * n) ^ (2 * t) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
    _ = _ := by rw [mul_pow]; ring

theorem rK_le (n : ℕ) (hn : 1 ≤ n) :
    (parameters q t n).r * (parameters q t n).K + 1 ≤
      ((2 * t + 1) * (2 * q * (2 * t + 2)) ^ (2 * t) * ceilLog 2 q + 1) * n ^ (2 * t + 1) := by
  have h := r_le q t hq ht n hn
  have hK : (parameters q t n).K = n * ceilLog 2 q := rfl
  rw [hK]
  set A := (2 * t + 1) * (2 * q * (2 * t + 2)) ^ (2 * t)
  have h1 : 1 ≤ n ^ (2 * t + 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : (parameters q t n).r * (n * ceilLog 2 q) ≤ A * n ^ (2 * t) * (n * ceilLog 2 q) :=
    Nat.mul_le_mul_right _ h
  have h3 : A * n ^ (2 * t) * (n * ceilLog 2 q) = A * ceilLog 2 q * n ^ (2 * t + 1) := by ring
  rw [add_mul, one_mul]
  omega

/-- `B + 1 = O(log n)`. -/
theorem B_bound : ∃ cB : ℝ, 1 ≤ cB ∧ ∀ n : ℕ, 3 ≤ n →
    (((parameters q t n).B + 1 : ℕ) : ℝ) ≤ cB * Real.log n := by
  set A2 := (2 * t + 1) * (2 * q * (2 * t + 2)) ^ (2 * t) * ceilLog 2 q + 1 with hA2
  have hA2 : 1 ≤ A2 := by omega
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlA : 0 ≤ Real.log A2 := Real.log_nonneg (by exact_mod_cast hA2)
  set cb := (Real.log A2 + (2 * t + 1 : ℕ) + Real.log 2) / Real.log 2 with hcb
  have hcb0 : 0 ≤ cb := by positivity
  refine ⟨2 * cb + 1, by linarith, fun n hn => ?_⟩
  have hℓ := one_le_log hn
  set X := (parameters q t n).r * (parameters q t n).K + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hXle := rK_le q t hq ht n (by omega)
  have hB : (parameters q t n).B = 2 * ceilLog 2 X := rfl
  have h1 := ceilLog_mul_log_le 2 X le_rfl hX1
  have h2 : Real.log X ≤ Real.log A2 + (2 * t + 1 : ℕ) * Real.log n := by
    rw [← Real.log_pow, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by exact_mod_cast hX1)
    exact_mod_cast hXle
  have h3 : (ceilLog 2 X : ℝ) ≤ cb * Real.log n := by
    rw [hcb, div_mul_eq_mul_div, le_div_iff₀ hl2]
    push_cast at h1 h2 ⊢
    have : 0 ≤ Real.log (A2 : ℝ) := hlA
    nlinarith
  rw [hB]; push_cast
  nlinarith

/-- `log L = 2t log n + O(log log n)`. -/
theorem L_bound : ∃ a0 : ℝ, 0 ≤ a0 ∧ ∀ n : ℕ, 3 ≤ n →
    1 ≤ (parameters q t n).L ∧ (parameters q t n).L / 2 * 2 = (parameters q t n).L ∧
    (2 * t : ℕ) * Real.log n ≤ Real.log (parameters q t n).L ∧
    Real.log (parameters q t n).L ≤ a0 + (2 * t : ℕ) * Real.log n + Real.log (Real.log n) := by
  obtain ⟨cB, hcB, hB⟩ := B_bound q t hq ht
  set A1 := (2 * t + 1) * (2 * q * (2 * t + 2)) ^ (2 * t) with hA1
  have hA1 : 1 ≤ A1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨Real.log (8 * A1 * cB), Real.log_nonneg (by
    have : (1 : ℝ) ≤ A1 := by exact_mod_cast hA1
    nlinarith), fun n hn => ?_⟩
  have hL : (parameters q t n).L = 4 * ((parameters q t n).r + 1) * ((parameters q t n).B + 1) := rfl
  have hr1 := r_ge q t hq ht n
  have hr2 := r_le q t hq ht n (by omega)
  have hn2 : 1 ≤ n ^ (2 * t) := Nat.one_le_pow _ _ (by omega)
  have hℓ := one_le_log hn
  have hLpos1 : 1 ≤ (parameters q t n).L := by
    rw [hL]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨hLpos1, ?_, ?_, ?_⟩
  · rw [hL]
    exact Nat.div_mul_cancel (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _)
  · rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    have : n ^ (2 * t) ≤ (parameters q t n).L := by
      rw [hL]
      calc n ^ (2 * t) ≤ (parameters q t n).r := hr1
        _ ≤ 4 * ((parameters q t n).r + 1) * ((parameters q t n).B + 1) := by nlinarith
    exact_mod_cast this
  · have hBn := hB n hn
    have hLle : ((parameters q t n).L : ℝ) ≤ (8 * A1 * cB) * ((n : ℝ) ^ (2 * t) * Real.log n) := by
      have h1 : ((parameters q t n).L : ℝ) ≤
          8 * (parameters q t n).r * (((parameters q t n).B + 1 : ℕ) : ℝ) := by
        rw [hL]; push_cast
        have : (1 : ℝ) ≤ (parameters q t n).r := by exact_mod_cast le_trans hn2 hr1
        have : (0 : ℝ) ≤ (parameters q t n).B := by positivity
        nlinarith
      have h2 : ((parameters q t n).r : ℝ) ≤ A1 * (n : ℝ) ^ (2 * t) := by exact_mod_cast hr2
      have h3 : (0 : ℝ) ≤ (((parameters q t n).B + 1 : ℕ) : ℝ) := by positivity
      calc ((parameters q t n).L : ℝ) ≤ 8 * (parameters q t n).r * (((parameters q t n).B + 1 : ℕ) : ℝ) := h1
        _ ≤ 8 * (A1 * (n : ℝ) ^ (2 * t)) * (cB * Real.log n) := by
          apply mul_le_mul (by linarith) hBn h3 (by positivity)
        _ = _ := by ring
    have hpos : (0 : ℝ) < (parameters q t n).L := by
      exact_mod_cast hLpos1
    calc Real.log (parameters q t n).L ≤ Real.log ((8 * A1 * cB) * ((n : ℝ) ^ (2 * t) * Real.log n)) :=
          Real.log_le_log hpos hLle
      _ = _ := by
        have : (0 : ℝ) < 8 * A1 * cB := by
          have : (1 : ℝ) ≤ A1 := by exact_mod_cast hA1
          positivity
        rw [Real.log_mul this.ne' (by positivity : (n : ℝ) ^ (2 * t) * Real.log n ≠ 0),
          Real.log_mul (by positivity : (n : ℝ) ^ (2 * t) ≠ 0) (ne_of_gt (by linarith)),
          Real.log_pow]
        push_cast; ring

/-- `log p_{L-1} = 2t log n + O(log log n)`. -/
theorem p_bound : ∃ a1 : ℝ, 0 ≤ a1 ∧ ∀ n : ℕ, 3 ≤ n →
    Real.log (parameters q t n).L ≤ Real.log (primeAt ((parameters q t n).L - 1)) ∧
    Real.log (primeAt ((parameters q t n).L - 1)) ≤
      a1 + (2 * t : ℕ) * Real.log n + 2 * Real.log (Real.log n) := by
  obtain ⟨a0, ha0, hLb⟩ := L_bound q t hq ht
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set cL := a0 + (2 * t : ℕ) + 1 with hcL
  set cp := 8 + 2 * cL / Real.log 2 with hcp
  have hcL0 : 0 ≤ cL := by positivity
  have hcp1 : 1 ≤ cp := by have : 0 ≤ 2 * cL / Real.log 2 := by positivity
                           linarith
  refine ⟨Real.log 2 + a0 + Real.log cp, by
    have := Real.log_nonneg hcp1; linarith, fun n hn => ?_⟩
  obtain ⟨hL1, -, hLlo, hLhi⟩ := hLb n hn
  have hℓ := one_le_log hn
  have hll0 := loglog_nonneg hn
  have hll := loglog_le_log hn
  set L := (parameters q t n).L with hLdef
  set p := primeAt (L - 1) with hp
  have hp1 : L ≤ p := by
    have := Nat.add_two_le_nth_prime (L - 1); simp only [hp, primeAt]; omega
  have hp2 : p ≤ (L + 1) * (2 * (Nat.log 2 (L + 1) + 3)) := by
    have := nth_prime_le (L - 1)
    rwa [show L - 1 + 2 = L + 1 by omega] at this
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  refine ⟨Real.log_le_log hLpos (by exact_mod_cast hp1), ?_⟩
  -- log L ≤ cL log n
  have hLc : Real.log L ≤ cL * Real.log n := by
    rw [hcL]; push_cast at hLhi ⊢; nlinarith
  have hL1' : Real.log ((L + 1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log L := by
    rw [← Real.log_mul (by norm_num) hLpos.ne']
    apply Real.log_le_log (by positivity)
    push_cast
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    linarith
  have hfl := floorLog_mul_log_le 2 (L + 1) le_rfl (by omega)
  unfold floorLog at hfl
  rw [Nat.cast_ofNat] at hfl
  have hfac : (((2 * (Nat.log 2 (L + 1) + 3)) : ℕ) : ℝ) ≤ cp * Real.log n := by
    push_cast
    have h1 : (Nat.log 2 (L + 1) : ℝ) ≤ (Real.log 2 + cL * Real.log n) / Real.log 2 := by
      rw [le_div_iff₀ hl2]; linarith
    have h2 : (Real.log 2 + cL * Real.log n) / Real.log 2 = 1 + cL / Real.log 2 * Real.log n := by
      field_simp
    rw [h2] at h1
    rw [hcp]
    have : 0 ≤ cL / Real.log 2 := by positivity
    have : 2 * cL / Real.log 2 = 2 * (cL / Real.log 2) := by ring
    nlinarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le hL1 hp1)
  have hfac0 : (0 : ℝ) < (((2 * (Nat.log 2 (L + 1) + 3)) : ℕ) : ℝ) := by positivity
  have hlp : Real.log p ≤ Real.log ((L + 1 : ℕ) : ℝ) +
      Real.log (((2 * (Nat.log 2 (L + 1) + 3)) : ℕ) : ℝ) := by
    rw [← Real.log_mul (by positivity) hfac0.ne']
    apply Real.log_le_log hp0
    exact_mod_cast hp2
  have hlf : Real.log (((2 * (Nat.log 2 (L + 1) + 3)) : ℕ) : ℝ) ≤
      Real.log cp + Real.log (Real.log n) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log hfac0 hfac
  linarith

end

end EditMulticoloring.Dev.Redundancy
end

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Redundancy
open EditMulticoloring.Code

/-- Real-arithmetic step: `h = O(log n)`. -/
theorem real_h (lq τ ℓ ll a1 cL h1 h2 logL logp : ℝ) (hlq : 0 < lq) (ha1 : 0 ≤ a1)
    (hℓ : 1 ≤ ℓ) (hll : ll ≤ ℓ)
    (e1 : h1 * lq ≤ logL + lq) (e2 : h2 * lq ≤ logp + lq)
    (hphi : logp ≤ a1 + τ * ℓ + 2 * ll) (hLc : logL ≤ cL * ℓ) :
    h1 + h2 ≤ (cL + a1 + τ + 2 + 2 * lq) / lq * ℓ := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hlq]
  have h1' := mul_le_mul_of_nonneg_left hℓ ha1
  have h2' := mul_le_mul_of_nonneg_left hℓ hlq.le
  have : (cL + a1 + τ + 2 + 2 * lq) * ℓ = cL * ℓ + a1 * ℓ + τ * ℓ + 2 * ℓ + 2 * (lq * ℓ) := by ring
  rw [this, add_mul]
  linarith

/-- Real-arithmetic step: the two-sided redundancy estimate, multiplied by `log q`. -/
theorem real_main (lq l2 τ ℓ ll a1 C' lch h1 h2 ρ fl logL logp : ℝ) (hlq : 0 < lq)
    (hC' : 0 < C') (hll1 : 1 ≤ ll) (hlch : 0 ≤ lch) (hl2 : 0 ≤ l2) (ha1 : 0 ≤ a1)
    (e1 : h1 * lq ≤ logL + lq) (e2 : h2 * lq ≤ logp + lq) (e2' : logp ≤ h2 * lq)
    (e3 : logL - l2 < (fl + 1) * lq) (e4 : fl ≤ h1)
    (hLlo : τ * ℓ ≤ logL) (hLp : logL ≤ logp) (hphi : logp ≤ a1 + τ * ℓ + 2 * ll)
    (hhρ : h1 + h2 ≤ ρ) (hρ : ρ ≤ h1 + h2 + C' * (lch + ll)) :
    τ * ℓ ≤ (ρ - fl) * lq ∧
    (ρ - fl) * lq - τ * ℓ ≤ (a1 + 2 + 3 * lq + l2 + lq * (C' * (lch + 1))) * ll := by
  constructor
  · have := mul_le_mul_of_nonneg_left (show h2 ≤ ρ - fl by linarith) hlq.le
    nlinarith
  · have hx := mul_le_mul_of_nonneg_left hρ hlq.le
    have h3 := mul_le_mul_of_nonneg_left hll1 ha1
    have h4 := mul_le_mul_of_nonneg_left hll1 hlq.le
    have h5 := mul_le_mul_of_nonneg_left hll1 hl2
    have h6 := mul_le_mul_of_nonneg_left hll1 (mul_nonneg (mul_nonneg hlq.le hC'.le) hlch)
    have : (a1 + 2 + 3 * lq + l2 + lq * (C' * (lch + 1))) * ll =
        a1 * ll + 2 * ll + 3 * (lq * ll) + l2 * ll + (lq * C' * lch) * ll + lq * C' * ll := by ring
    rw [this]
    have : lq * (h1 + h2 + C' * (lch + ll)) =
        h1 * lq + h2 * lq + lq * C' * lch + lq * C' * ll := by ring
    rw [this] at hx
    have : (ρ - fl) * lq = ρ * lq - fl * lq := by ring
    rw [this]
    have : ρ * lq = lq * ρ := by ring
    rw [this]
    nlinarith

/-- The analytic core: `ρ < n` and `ρ - ⌊log_q (L/2)⌋ = 2t log_q n + O(log log n)`. -/
theorem redundancy_core (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 27 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (parameters q t n).ρ < n ∧
      |((parameters q t n).ρ : ℝ) - (floorLog q ((parameters q t n).L / 2) : ℕ) -
          (2 * t : ℕ) * logBase q n| ≤ C * Real.log (Real.log (n : ℝ)) := by
  obtain ⟨C', hC', HS⟩ := short_edit_code q t hq ht
  obtain ⟨a0, ha0, hLb⟩ := L_bound q t hq ht
  obtain ⟨a1, ha1, hpb⟩ := p_bound q t hq ht
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set cL : ℝ := a0 + (2 * t : ℕ) + 1 with hcL
  have hcL0 : 0 ≤ cL := by positivity
  set ch : ℝ := (cL + a1 + (2 * t : ℕ) + 2 + 2 * Real.log q) / Real.log q with hch
  have hch0 : 0 ≤ ch := by positivity
  have hlch : 0 ≤ Real.log (ch + 1) := Real.log_nonneg (by linarith)
  set cρ : ℝ := ch + C' * Real.log (ch + 1) + C' with hcρ
  have hcρ0 : 0 ≤ cρ := by positivity
  set Cn : ℝ := a1 + 2 + 3 * Real.log q + Real.log 2 +
    Real.log q * (C' * (Real.log (ch + 1) + 1)) with hCn
  have hCn0 : 0 < Cn := by positivity
  obtain ⟨N, hN⟩ := eventually_lt cρ hcρ0
  refine ⟨Cn / Real.log q, by positivity, max 27 N, le_max_left _ _, fun n hn => ?_⟩
  have hn27 : 27 ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := by omega
  have hℓ := one_le_log hn3
  have hll0 := loglog_nonneg hn3
  have hll := loglog_le_log hn3
  have hll1 := one_le_loglog hn27
  obtain ⟨hL1, hL2, hLlo, hLhi⟩ := hLb n hn3
  obtain ⟨hLp, hphi⟩ := hpb n hn3
  set P := parameters q t n with hP
  have hh : P.h = P.h₁ + P.h₂ := rfl
  have hh1 : P.h₁ = ceilLog q P.L := rfl
  have hh2 : P.h₂ = ceilLog q (primeAt (P.L - 1)) := rfl
  have hρdef : P.ρ = shortLength q t P.h := rfl
  have hhpos : 1 ≤ P.h := Dev.Decoder.h_pos q t n hq
  obtain ⟨-, ⟨hhρ, -⟩, -, hρC, -⟩ := HS P.h hhpos
  rw [← hρdef] at hhρ hρC
  have hp1 : 1 ≤ primeAt (P.L - 1) := Dev.Decoder.primeAt_pos _
  -- the three integer logarithms
  have e1 : (P.h₁ : ℝ) * Real.log q ≤ Real.log P.L + Real.log q := by
    rw [hh1]; exact ceilLog_mul_log_le q _ hq hL1
  have e2 : (P.h₂ : ℝ) * Real.log q ≤ Real.log (primeAt (P.L - 1)) + Real.log q := by
    rw [hh2]; exact ceilLog_mul_log_le q _ hq hp1
  have e2' : Real.log (primeAt (P.L - 1)) ≤ (P.h₂ : ℝ) * Real.log q := by
    rw [hh2]; exact log_le_ceilLog_mul q _ hq hp1
  set fl := floorLog q (P.L / 2) with hfl
  have hL2' : 1 ≤ P.L / 2 := by omega
  have e3 : Real.log P.L - Real.log 2 < ((fl : ℝ) + 1) * Real.log q := by
    have := log_lt_floorLog_succ q (P.L / 2) hq hL2'
    have h' : Real.log P.L = Real.log ((P.L / 2 : ℕ) : ℝ) + Real.log 2 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      congr 1
      exact_mod_cast hL2.symm
    linarith
  have e4 : fl ≤ P.h₁ := by
    rw [hh1, hfl]
    exact le_trans (Nat.log_mono_right (Nat.div_le_self _ _)) (floorLog_le_ceilLog q P.L)
  have hLc : Real.log P.L ≤ cL * Real.log n := by
    rw [hcL]; push_cast at hLhi ⊢; nlinarith
  -- `h = O(log n)`
  have hhr : (P.h : ℝ) = P.h₁ + P.h₂ := by rw [hh]; push_cast; ring
  have hhl : (P.h : ℝ) ≤ ch * Real.log n := by
    rw [hhr, hch]
    exact real_h _ _ _ _ _ _ _ _ _ _ hlq ha1 hℓ hll e1 e2 hphi hLc
  have hlh : Real.log ((P.h : ℝ) + 1) ≤ Real.log (ch + 1) + Real.log (Real.log n) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hρ' : (P.ρ : ℝ) ≤ (P.h : ℝ) + C' * (Real.log (ch + 1) + Real.log (Real.log n)) := by
    have := mul_le_mul_of_nonneg_left hlh hC'.le
    linarith
  refine ⟨?_, ?_⟩
  · have h1 : (P.ρ : ℝ) ≤ cρ * Real.log n := by
      rw [hcρ]
      have := mul_le_mul_of_nonneg_left hll hC'.le
      have := mul_le_mul_of_nonneg_left hℓ (mul_nonneg hC'.le hlch)
      nlinarith
    have h2 := hN n (le_trans (le_max_right _ _) hn)
    exact_mod_cast (lt_of_le_of_lt h1 h2)
  · have hρh : (P.h : ℝ) ≤ P.ρ := by exact_mod_cast hhρ
    have hfle : (fl : ℝ) ≤ P.h₁ := by exact_mod_cast e4
    have hlb : logBase q n = Real.log n / Real.log q := rfl
    obtain ⟨key_lo, key_hi⟩ := real_main (ρ := (P.ρ : ℝ)) (fl := (fl : ℝ)) _ _ _ _ _ _ _ _ _ _ _ _ hlq hC' hll1 hlch hl2.le ha1
      e1 e2 e2' e3 hfle hLlo hLp hphi (by rw [← hhr]; exact hρh) (by rw [← hhr]; exact hρ')
    rw [← hCn] at key_hi
    rw [abs_le, hlb]
    have hCq : Cn / Real.log q * Real.log (Real.log n) =
        (Cn * Real.log (Real.log n)) / Real.log q := by ring
    have hsplit : (P.ρ : ℝ) - fl - (2 * t : ℕ) * (Real.log n / Real.log q) =
        (((P.ρ : ℝ) - fl) * Real.log q - (2 * t : ℕ) * Real.log n) / Real.log q := by
      rw [eq_div_iff hlq.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hlq.ne']
    rw [hCq, hsplit]
    constructor
    · have h1 : 0 ≤ (((P.ρ : ℝ) - fl) * Real.log q - (2 * t : ℕ) * Real.log n) / Real.log q :=
        div_nonneg (by linarith) hlq.le
      have h2 : 0 ≤ Cn * Real.log (Real.log n) / Real.log q := by positivity
      linarith
    · exact div_le_div_of_nonneg_right key_hi hlq.le

end EditMulticoloring.Dev.Redundancy

namespace EditMulticoloring.Code

open EditMulticoloring.Dev.Redundancy in
theorem chk_encoder_redundancy (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      let P := parameters q t n
      1 ≤ P.m ∧ P.m + P.ρ = n ∧
      ∀ p : ℕ, ValidModulus (ceilLog 2 (P.r * P.K + 1)) p →
        (∀ u : FixedWord q P.k, (encode t n p (toWord u)).length = n) ∧
        Function.Injective (fun u : FixedWord q P.k => encode t n p (toWord u)) ∧
        (code q t n p).card = P.J * q ^ P.m ∧
        (code q t n p).card = q ^ P.k ∧
        |((n : ℝ) - (P.k : ℝ)) - (2 * t : ℕ) * logBase q n| ≤
          C * Real.log (Real.log (n : ℝ)) := by
  obtain ⟨C, hC, n₀, hn₀, H⟩ := redundancy_core q t hq ht
  refine ⟨C, hC, n₀, by omega, fun n hn => ?_⟩
  obtain ⟨hρn, hest⟩ := H n hn
  dsimp only
  set P := parameters q t n with hP
  have hmdef : P.m = n - P.ρ := rfl
  have hm : 1 ≤ P.m := by omega
  have hk : P.k = P.m + floorLog q (P.L / 2) := by
    show P.m + floorLog q (q ^ floorLog q (P.L / 2)) = _
    unfold floorLog
    rw [Nat.log_pow (by omega)]
  have hkJ : q ^ P.k = P.J * q ^ P.m := by
    have : P.J = q ^ floorLog q (P.L / 2) := rfl
    rw [hk, this, pow_add, mul_comm]
  refine ⟨hm, by omega, fun p hp => ?_⟩
  have hlen : ∀ u : FixedWord q P.k, (encode t n p (toWord u)).length = n := fun u =>
    Dev.Decoder.encode_length q t n p hq ht hm hp _ (Dev.Decoder.length_toWord u)
  have hval : ∀ w : Word q, w.length = P.k → validate t n p (encode t n p w) = some w :=
    fun w hw => Dev.Decoder.validate_encode q t n p hq ht hm hp w hw
  have hcard : (code q t n p).card = q ^ P.k := by
    unfold code
    rw [List.toFinset_card_of_nodup, List.length_map, words_length]
    refine (words_nodup q _).map_on ?_
    intro x hx y hy hxy
    have h1 := hval x ((mem_words x).1 hx)
    have h2 := hval y ((mem_words y).1 hy)
    rw [hxy, h2] at h1
    exact (Option.some_inj.1 h1).symm
  refine ⟨hlen, ?_, by rw [hcard, hkJ], hcard, ?_⟩
  · intro u v huv
    have h1 := hval _ (Dev.Decoder.length_toWord u)
    have h2 := hval _ (Dev.Decoder.length_toWord v)
    simp only at huv
    rw [huv, h2] at h1
    exact Dev.Decoder.toWord_inj (Option.some_inj.1 h1).symm
  · have hnk : (n : ℝ) - (P.k : ℝ) = (P.ρ : ℝ) - (floorLog q (P.L / 2) : ℕ) := by
      have : n = P.m + P.ρ := by omega
      rw [hk, this]; push_cast; ring
    rw [hnk]
    exact hest

end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_encoder_redundancy := @EditMulticoloring.Code.chk_encoder_redundancy
