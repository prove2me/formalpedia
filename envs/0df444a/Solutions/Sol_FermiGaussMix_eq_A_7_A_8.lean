-- Prove2me | solution 1 for FermiGaussMix.eq_A_7_A_8
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:25:04.298142+00:00
-- url     : https://prove2.me/submissions/0fb30489-7884-4d55-afb7-bbd87366281c

import Mathlib
import Definitions.Def_FermiGaussMix_coeff


/- Source module Solutions/Fermi777Majorana.lean -/

set_option autoImplicit false

namespace FermiGaussMix.MajoranaProof

open Matrix FermiCap.Gaussian
open scoped BigOperators

theorem pauliString_mul {n : ℕ} (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    pauliString A * pauliString B = pauliString (fun i => A i * B i) := by
  classical
  ext y x
  simp only [Matrix.mul_apply, pauliString, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (b : Fin 2) =>
    A i (y i) b * B i b (x i))).symm

theorem pauliString_one (n : ℕ) :
    pauliString (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  classical
  ext y x
  by_cases h : y = x
  · subst x
    simp [pauliString]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hi

theorem pauliString_star {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    star (pauliString A) = pauliString (fun i => star (A i)) := by
  ext x y
  simp [Matrix.star_apply, pauliString]

private theorem pauli_square :
    pauliX * pauliX = 1 ∧ pauliY * pauliY = 1 ∧ pauliZ * pauliZ = 1 := by
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;> norm_num [pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;> norm_num [pauliY, Matrix.mul_apply, Fin.sum_univ_two]
  · ext a b
    fin_cases a <;> fin_cases b <;> norm_num [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pauli_selfAdjoint :
    star pauliX = pauliX ∧ star pauliY = pauliY ∧ star pauliZ = pauliZ := by
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [pauliX, Matrix.star_apply]
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [pauliY, Matrix.star_apply]
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [pauliZ, Matrix.star_apply]

private theorem pauli_anticommute :
    pauliX * pauliY = -(pauliY * pauliX) ∧
    pauliX * pauliZ = -(pauliZ * pauliX) ∧
    pauliY * pauliZ = -(pauliZ * pauliY) := by
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;> norm_num [pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;> norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · ext a b
    fin_cases a <;> fin_cases b <;> norm_num [pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem majorana_square {n : ℕ} (p : Fin (2 * n)) :
    majorana n p * majorana n p = 1 := by
  unfold majorana
  rw [pauliString_mul, ← pauliString_one n]
  congr 1
  funext k
  split_ifs <;> simp_all [pauli_square.1, pauli_square.2.1, pauli_square.2.2]

theorem majorana_star {n : ℕ} (p : Fin (2 * n)) :
    star (majorana n p) = majorana n p := by
  unfold majorana
  rw [pauliString_star]
  congr 1
  funext k
  split_ifs <;> simp_all [pauli_selfAdjoint.1, pauli_selfAdjoint.2.1,
    pauli_selfAdjoint.2.2]

theorem majorana_unitary {n : ℕ} (p : Fin (2 * n)) :
    majorana n p ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  constructor <;> rw [majorana_star, majorana_square]

private def localOp {n : ℕ} (p : Fin (2 * n)) (k : Fin n) : Matrix (Fin 2) (Fin 2) ℂ :=
  if k.val < p.val / 2 then pauliZ
  else if k.val = p.val / 2 then (if p.val % 2 = 0 then pauliX else pauliY)
  else 1

private theorem localOp_anticommute {n : ℕ} (p q : Fin (2 * n)) (hpq : p < q)
    (k : Fin n) :
    localOp p k * localOp q k =
      if k.val = p.val / 2 then -(localOp q k * localOp p k)
      else localOp q k * localOp p k := by
  have hdiv : p.val / 2 ≤ q.val / 2 := Nat.div_le_div_right (le_of_lt hpq)
  by_cases hkp : k.val < p.val / 2
  · have hkq : k.val < q.val / 2 := lt_of_lt_of_le hkp hdiv
    simp [localOp, hkp, hkq, ne_of_lt hkp]
  by_cases hke : k.val = p.val / 2
  · by_cases hlt : p.val / 2 < q.val / 2
    · have hkq : k.val < q.val / 2 := hke ▸ hlt
      by_cases hp0 : p.val % 2 = 0
      · simp [localOp, hke, hlt, hp0, pauli_anticommute.2.1]
      · simp [localOp, hke, hlt, hp0, pauli_anticommute.2.2]
    · have hdeq : p.val / 2 = q.val / 2 := le_antisymm hdiv (Nat.le_of_not_gt hlt)
      have hp0 : p.val % 2 = 0 := by omega
      have hq1 : q.val % 2 = 1 := by omega
      have hkeq : k.val = q.val / 2 := hke.trans hdeq
      simp [localOp, hke, hlt, hdeq, hp0, hq1, pauli_anticommute.1]
  · have hpeq : localOp p k = 1 := by simp [localOp, hkp, hke]
    simp [hpeq, hke]

private theorem pauliString_neg_at {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (t : Fin n) :
    pauliString (fun k => if k = t then -A k else A k) = -pauliString A := by
  classical
  ext x y
  change (∏ k, (if k = t then -A k else A k) (x k) (y k)) = -(∏ k, A k (x k) (y k))
  have h : ∀ k, (if k = t then -A k else A k) (x k) (y k) =
      (if k = t then (-1 : ℂ) else 1) * A k (x k) (y k) := by
    intro k
    by_cases hk : k = t <;> simp [hk]
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

theorem majorana_anticommute_lt {n : ℕ} (p q : Fin (2 * n)) (hpq : p < q) :
    majorana n p * majorana n q = -(majorana n q * majorana n p) := by
  let t : Fin n := ⟨p.val / 2, by omega⟩
  change pauliString (localOp p) * pauliString (localOp q) =
    -(pauliString (localOp q) * pauliString (localOp p))
  rw [pauliString_mul, pauliString_mul]
  have h : (fun k => localOp p k * localOp q k) =
      fun k => if k = t then -(localOp q k * localOp p k) else localOp q k * localOp p k := by
    funext k
    simpa only [Fin.ext_iff, t] using localOp_anticommute p q hpq k
  rw [h, pauliString_neg_at]

theorem majorana_anticommute {n : ℕ} (p q : Fin (2 * n)) (hpq : p ≠ q) :
    majorana n p * majorana n q = -(majorana n q * majorana n p) := by
  rcases lt_or_gt_of_ne hpq with h | h
  · exact majorana_anticommute_lt p q h
  · have hh := congrArg Neg.neg (majorana_anticommute_lt q p h)
    simpa only [neg_neg] using hh.symm

open scoped Matrix.Norms.L2Operator

theorem monomial_unitary {n : ℕ} (x : Fin (2 * n) → Bool) :
    monomial n x ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold monomial
  apply list_prod_mem
  intro A hA
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hA
  split_ifs
  · exact majorana_unitary p
  · exact one_mem _

theorem norm_P {n : ℕ} (R : Finset (Fin (2 * n))) : ‖P n R‖ = 1 := by
  rw [P, norm_smul, norm_pow, Complex.norm_I, one_pow,
    CStarRing.norm_of_mem_unitary (monomial_unitary _), mul_one]

theorem norm_entry_le_operator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  have h1 := PiLp.norm_apply_le
    ((EuclideanSpace.equiv ι ℂ).symm (A *ᵥ EuclideanSpace.single j 1)) i
  have h2 := A.l2_opNorm_mulVec (EuclideanSpace.single j (1 : ℂ))
  have h : ‖((EuclideanSpace.equiv ι ℂ).symm
      (A *ᵥ EuclideanSpace.single j (1 : ℂ))) i‖ ≤ ‖A‖ * ‖EuclideanSpace.single j (1 : ℂ)‖ :=
    h1.trans h2
  simpa [EuclideanSpace.single, Matrix.mulVec_single_one] using h

theorem norm_trace_le_card_mul_operator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A.trace‖ ≤ Fintype.card ι * ‖A‖ := by
  calc
    ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖A‖ := Finset.sum_le_sum fun i _ => norm_entry_le_operator A i i
    _ = Fintype.card ι * ‖A‖ := by simp

theorem norm_coeff_le_operator {n : ℕ} (O : Op n) (R : Finset (Fin (2 * n))) :
    ‖coeff O R‖ ≤ ‖O‖ := by
  have hpos : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have hcard : (Fintype.card (Qubits n) : ℝ) = (2 : ℝ) ^ n := by
    simp [Qubits, Fintype.card_fun]
  calc
    ‖coeff O R‖ = (2 : ℝ)⁻¹ ^ n * ‖(P n R * O).trace‖ := by simp [coeff, norm_mul]
    _ ≤ (2 : ℝ)⁻¹ ^ n * (Fintype.card (Qubits n) * ‖P n R * O‖) :=
      mul_le_mul_of_nonneg_left (norm_trace_le_card_mul_operator _) hpos
    _ ≤ (2 : ℝ)⁻¹ ^ n * (Fintype.card (Qubits n) * (‖P n R‖ * ‖O‖)) := by
      gcongr
      exact norm_mul_le _ _
    _ = ‖O‖ := by
      rw [hcard, norm_P]
      simp [← mul_assoc, ← mul_pow]

end FermiGaussMix.MajoranaProof


/- Source module Solutions/Fermi777Monomial.lean -/

set_option autoImplicit false

namespace FermiGaussMix.MajoranaProof

open Matrix FermiCap.Gaussian
open scoped BigOperators
noncomputable section

def word {n : ℕ} (l : List (Fin (2 * n))) : Op n := (l.map (majorana n)).prod

def shiftSign {n : ℕ} (c : Fin (2 * n)) (l : List (Fin (2 * n))) : ℂ :=
  (l.map fun b => if c = b then (1 : ℂ) else -1).prod

theorem majorana_word (n : ℕ) (c : Fin (2 * n)) (l : List (Fin (2 * n))) :
    majorana n c * word l = shiftSign c l • (word l * majorana n c) := by
  induction l with
  | nil => simp [word, shiftSign]
  | cons a l ih =>
    have hca : majorana n c * majorana n a =
        (if c = a then (1 : ℂ) else -1) • (majorana n a * majorana n c) := by
      by_cases h : c = a
      · simp [h]
      · simp [h, majorana_anticommute c a h]
    change majorana n c * (majorana n a * word l) =
      ((if c = a then (1 : ℂ) else -1) * shiftSign c l) •
        ((majorana n a * word l) * majorana n c)
    rw [← mul_assoc, hca, smul_mul_assoc, mul_assoc, ih,
      mul_smul_comm, smul_smul, mul_assoc]

theorem shiftSign_of_not_mem {n : ℕ} (c : Fin (2 * n))
    (l : List (Fin (2 * n))) (h : c ∉ l) : shiftSign c l = (-1 : ℂ) ^ l.length := by
  induction l with
  | nil => simp [shiftSign]
  | cons a l ih =>
    have hc : c ≠ a := by simpa using fun hc => h (List.mem_cons.mpr (Or.inl hc))
    have hl : c ∉ l := fun hc => h (List.mem_cons.mpr (Or.inr hc))
    simpa [shiftSign, hc, pow_succ, mul_comm] using congrArg (fun z : ℂ => -z) (ih hl)

theorem majorana_commute_even_word {n : ℕ} (c : Fin (2 * n))
    (l : List (Fin (2 * n))) (h : c ∉ l) (he : Even l.length) :
    majorana n c * word l = word l * majorana n c := by
  rw [majorana_word, shiftSign_of_not_mem c l h, he.neg_one_pow, one_smul]

def canonical {n : ℕ} (l : List (Fin (2 * n))) : Op n :=
  Complex.I ^ (l.length / 2) • word l

theorem majorana_commute_canonical {n : ℕ} (c : Fin (2 * n))
    (l : List (Fin (2 * n))) (h : c ∉ l) (he : Even l.length) :
    majorana n c * canonical l = canonical l * majorana n c := by
  simp only [canonical, mul_smul_comm, smul_mul_assoc,
    majorana_commute_even_word c l h he]

theorem canonical_cons_cons {n : ℕ} (a b : Fin (2 * n)) (l : List (Fin (2 * n))) :
    canonical (a :: b :: l) = Complex.I • ((majorana n a * majorana n b) * canonical l) := by
  change Complex.I ^ ((l.length + 1 + 1) / 2) •
      (majorana n a * (majorana n b * word l)) = _
  rw [show (l.length + 1 + 1) / 2 = l.length / 2 + 1 by omega, pow_succ]
  simp only [canonical, mul_smul_comm, smul_smul, mul_assoc]
  congr 1
  ring

theorem canonical_star {n : ℕ} (l : List (Fin (2 * n)))
    (hn : l.Nodup) (he : Even l.length) : star (canonical l) = canonical l := by
  induction l using List.twoStepInduction with
  | nil => simp [canonical, word]
  | singleton a => simp at he
  | cons_cons a b l ih _ =>
    obtain ⟨ha0, hbl⟩ := List.nodup_cons.mp hn
    obtain ⟨hb, hl⟩ := List.nodup_cons.mp hbl
    have hel : Even l.length := by
      obtain ⟨k, hk⟩ := he
      refine ⟨k - 1, ?_⟩
      simp only [List.length_cons] at hk
      omega
    have hab : b ≠ a := fun h => ha0 (by simp [h])
    have ha : a ∉ l := fun h => ha0 (by simp [h])
    rw [canonical_cons_cons, star_smul, star_mul, star_mul, ih hl hel,
      majorana_star, majorana_star, majorana_anticommute b a hab]
    simp only [Complex.star_def, Complex.conj_I, mul_neg, smul_neg, neg_smul, neg_neg]
    congr 1
    rw [← mul_assoc, ← majorana_commute_canonical a l ha hel, mul_assoc,
      ← majorana_commute_canonical b l hb hel, ← mul_assoc]

def supportWord {n : ℕ} (R : Finset (Fin (2 * n))) : List (Fin (2 * n)) :=
  (List.finRange (2 * n)).filter (fun p => p ∈ R)

theorem supportWord_nodup {n : ℕ} (R : Finset (Fin (2 * n))) : (supportWord R).Nodup :=
  (List.nodup_finRange _).filter _

theorem supportWord_toFinset {n : ℕ} (R : Finset (Fin (2 * n))) :
    (supportWord R).toFinset = R := by
  ext p
  simp [supportWord]

theorem supportWord_length {n : ℕ} (R : Finset (Fin (2 * n))) :
    (supportWord R).length = R.card := by
  rw [← List.toFinset_card_of_nodup (supportWord_nodup R), supportWord_toFinset]

theorem monomial_support {n : ℕ} (R : Finset (Fin (2 * n))) :
    word (supportWord R) = monomial n (fun p => decide (p ∈ R)) := by
  unfold word supportWord monomial
  generalize List.finRange (2 * n) = l
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a ∈ R <;> simp_all

theorem canonical_support {n : ℕ} (R : Finset (Fin (2 * n))) :
    canonical (supportWord R) = P n R := by
  rw [canonical, supportWord_length, monomial_support]
  rfl

theorem P_star {n : ℕ} (R : Finset (Fin (2 * n))) (hR : Even R.card) :
    star (P n R) = P n R := by
  rw [← canonical_support]
  exact canonical_star _ (supportWord_nodup R) (by simpa only [supportWord_length] using hR)

theorem P_unitary {n : ℕ} (R : Finset (Fin (2 * n))) :
    P n R ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold P
  apply Unitary.smul_mem_of_mem
  · apply (unitary ℂ).pow_mem
    constructor <;> simp [Complex.star_def, Complex.conj_I, Complex.I_sq]
  · exact monomial_unitary _

theorem P_square {n : ℕ} (R : Finset (Fin (2 * n))) (hR : Even R.card) :
    P n R * P n R = 1 := by
  simpa only [P_star R hR] using (P_unitary R).1

theorem shiftSign_of_mem {n : ℕ} (c : Fin (2 * n))
    (l : List (Fin (2 * n))) (hn : l.Nodup) (hc : c ∈ l) :
    shiftSign c l = (-1 : ℂ) ^ (l.length - 1) := by
  induction l with
  | nil => simp at hc
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hn
    by_cases hca : c = a
    · subst a
      simpa [shiftSign] using shiftSign_of_not_mem c l ha
    · have hcl : c ∈ l := (List.mem_cons.mp hc).resolve_left hca
      have hpos : 1 ≤ l.length := List.length_pos_iff.mpr (by
        intro hz
        simpa only [hz, List.not_mem_nil] using hcl)
      have hlen : l.length - 1 + 1 = l.length := Nat.sub_add_cancel hpos
      rw [show shiftSign c (a :: l) = (-1 : ℂ) * shiftSign c l by simp [shiftSign, hca]]
      change (-1 : ℂ) * shiftSign c l = (-1 : ℂ) ^ (l.length + 1 - 1)
      rw [ih hl hcl, Nat.add_sub_cancel]
      conv_rhs => rw [← hlen, pow_succ]
      ring

theorem majorana_P {n : ℕ} (c : Fin (2 * n))
    (R : Finset (Fin (2 * n))) (hR : Even R.card) :
    majorana n c * P n R =
      (if c ∈ R then (-1 : ℂ) else 1) • (P n R * majorana n c) := by
  have he : Even (supportWord R).length := by simpa only [supportWord_length] using hR
  have hs : shiftSign c (supportWord R) = if c ∈ R then (-1 : ℂ) else 1 := by
    by_cases hc : c ∈ R
    · have hcl : c ∈ supportWord R := by simpa [supportWord] using hc
      have hodd : Odd ((supportWord R).length - 1) := by
        obtain ⟨k, hk⟩ := he
        have hpos : 0 < (supportWord R).length := List.length_pos_of_mem hcl
        refine ⟨k - 1, ?_⟩
        omega
      rw [shiftSign_of_mem c _ (supportWord_nodup R) hcl, hodd.neg_one_pow, if_pos hc]
    · have hcl : c ∉ supportWord R := by simpa [supportWord] using hc
      rw [shiftSign_of_not_mem c _ hcl, he.neg_one_pow, if_neg hc]
  rw [← canonical_support R]
  simp only [canonical, mul_smul_comm, majorana_word, hs, smul_mul_assoc, smul_smul]
  congr 1
  ring

end
end FermiGaussMix.MajoranaProof


/- Source module Solutions/Fermi777Trace.lean -/

set_option autoImplicit false

namespace FermiGaussMix.MajoranaProof

open Matrix FermiCap.Gaussian
open scoped BigOperators Matrix.Norms.L2Operator

theorem trace_P_mul_ne {n : ℕ} (R T : Finset (Fin (2 * n)))
    (hR : Even R.card) (hT : Even T.card) (hne : R ≠ T) :
    (P n R * P n T).trace = 0 := by
  classical
  have hdiff : ∃ c, ¬ (c ∈ R ↔ c ∈ T) := by
    by_contra! h
    exact hne (Finset.ext h)
  obtain ⟨c, hc⟩ := hdiff
  have hanti : majorana n c * (P n R * P n T) =
      -((P n R * P n T) * majorana n c) := by
    rw [← mul_assoc, majorana_P c R hR, smul_mul_assoc, mul_assoc,
      majorana_P c T hT, mul_smul_comm, smul_smul]
    by_cases hr : c ∈ R
    · have ht : c ∉ T := fun ht => hc (iff_of_true hr ht)
      simp [hr, ht, mul_assoc]
    · have ht : c ∈ T := by tauto
      simp [hr, ht, mul_assoc]
  have heq : majorana n c * (P n R * P n T) * majorana n c = -(P n R * P n T) := by
    rw [hanti, neg_mul, mul_assoc, majorana_square, mul_one]
  have hcyc : (majorana n c * (P n R * P n T) * majorana n c).trace =
      (P n R * P n T).trace := by
    rw [mul_assoc, Matrix.trace_mul_comm (majorana n c), mul_assoc, majorana_square, mul_one]
  rw [heq, Matrix.trace_neg] at hcyc
  linear_combination (-1 / 2 : ℂ) * hcyc

theorem trace_P_orthogonal {n : ℕ} (R T : Finset (Fin (2 * n)))
    (hR : Even R.card) (hT : Even T.card) :
    (2 : ℂ)⁻¹ ^ n * (P n R * P n T).trace = if R = T then 1 else 0 := by
  classical
  by_cases h : R = T
  · subst T
    rw [P_square R hR, if_pos rfl, Matrix.trace_one]
    simp [Qubits]
  · rw [trace_P_mul_ne R T hR hT h, if_neg h, mul_zero]

theorem coeff_expansion {n : ℕ} (o : Finset (Fin (2 * n)) → ℂ)
    (R : Finset (Fin (2 * n))) (hR : Even R.card) :
    coeff (∑ T ∈ evenSets n, o T • P n T) R = o R := by
  classical
  calc
    coeff (∑ T ∈ evenSets n, o T • P n T) R =
        ∑ T ∈ evenSets n, o T * ((2 : ℂ)⁻¹ ^ n * (P n R * P n T).trace) := by
      simp [coeff, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
        Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = o R := by
      have h : ∀ T ∈ evenSets n,
          (2 : ℂ)⁻¹ ^ n * (P n R * P n T).trace = if R = T then 1 else 0 := by
        intro T hT
        exact trace_P_orthogonal R T hR ((Finset.mem_filter.mp hT).2)
      simp_rw [Finset.sum_congr rfl (fun T hT => congrArg (fun z : ℂ => o T * z) (h T hT))]
      simp [evenSets, hR]

end FermiGaussMix.MajoranaProof

namespace FermiGaussMix

open Matrix FermiCap.Gaussian
open scoped BigOperators Matrix.Norms.L2Operator

theorem eq_A_7_A_8_proof {n : ℕ} :
    (∀ R T : Finset (Fin (2 * n)), Even R.card → Even T.card →
      (2 : ℂ)⁻¹ ^ n * (P n R * P n T).trace = if R = T then 1 else 0) ∧
    (∀ (o : Finset (Fin (2 * n)) → ℂ) (R : Finset (Fin (2 * n))), Even R.card →
      coeff (∑ T ∈ evenSets n, o T • P n T) R = o R) ∧
    (∀ (O : Op n) (R : Finset (Fin (2 * n))), Even R.card → ‖coeff O R‖ ≤ ‖O‖) :=
  ⟨MajoranaProof.trace_P_orthogonal, MajoranaProof.coeff_expansion,
    fun O R _ => MajoranaProof.norm_coeff_le_operator O R⟩

end FermiGaussMix


open FermiGaussMix Matrix FermiCap.Gaussian
open scoped BigOperators Matrix.Norms.L2Operator
theorem solution {n : ℕ} :
    (∀ R T : Finset (Fin (2 * n)), Even R.card → Even T.card →
      (2 : ℂ)⁻¹ ^ n * (P n R * P n T).trace = if R = T then 1 else 0) ∧
    (∀ (o : Finset (Fin (2 * n)) → ℂ) (R : Finset (Fin (2 * n))), Even R.card →
      coeff (∑ T ∈ evenSets n, o T • P n T) R = o R) ∧
    (∀ (O : Op n) (R : Finset (Fin (2 * n))), Even R.card → ‖coeff O R‖ ≤ ‖O‖) := FermiGaussMix.eq_A_7_A_8_proof

#print axioms solution
