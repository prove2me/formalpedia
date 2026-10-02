-- Prove2me | solution 1 for DiscreteConvex.CombinatorialB.theorem_2_7_offdiag_diagdom_iff_translation_submodular
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T03:19:12.830024+00:00
-- url     : https://prove2.me/submissions/cb287971-31a0-41e2-ad4b-bc579b2513cb

import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
import Definitions.Def_DiscreteConvex_CombinatorialB_DiagDominance
import Definitions.Def_DiscreteConvex_CombinatorialB_Submodular
import Definitions.Def_DiscreteConvex_CombinatorialB_TranslationSubmodular
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/- Owned component: Solutions/QuadraticCore.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace QuadraticTranslationCore
open DiscreteConvex.CombinatorialB

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bilin (L : Matrix V V ℝ) (p q : V → ℝ) : ℝ :=
  dotProduct p (L.mulVec q)

noncomputable def rowSum (L : Matrix V V ℝ) (i : V) : ℝ := ∑ j, L i j

lemma bilin_symm (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    bilin L p q = bilin L q p := by
  simpa only [hL.eq, bilin] using Matrix.dotProduct_transpose_mulVec L p q

lemma bilin_add_left (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L (p+q) r = bilin L p r + bilin L q r := by
  simp only [bilin, add_dotProduct]

lemma bilin_add_right (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L p (q+r) = bilin L p q + bilin L p r := by
  simp only [bilin, Matrix.mulVec_add, dotProduct_add]

lemma bilin_sub_left (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L (p-q) r = bilin L p r - bilin L q r := by
  simp only [bilin, sub_dotProduct]

lemma bilin_sub_right (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L p (q-r) = bilin L p q - bilin L p r := by
  simp only [bilin, Matrix.mulVec_sub, dotProduct_sub]

lemma bilin_smul_left (L : Matrix V V ℝ) (a : ℝ) (p q : V → ℝ) :
    bilin L (a • p) q = a * bilin L p q := by
  simp only [bilin, smul_dotProduct, smul_eq_mul]

lemma bilin_smul_right (L : Matrix V V ℝ) (a : ℝ) (p q : V → ℝ) :
    bilin L p (a • q) = a * bilin L p q := by
  simp only [bilin, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma bilin_eq_sum (L : Matrix V V ℝ) (p q : V → ℝ) :
    bilin L p q = ∑ i, ∑ j, L i j * (p i * q j) := by
  simp only [bilin, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[simp] lemma qf_zero (L : Matrix V V ℝ) : QF L (0 : V → ℝ) = 0 := by
  simp [QF]

lemma qf_add (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L (p+q) = QF L p + QF L q + bilin L p q := by
  change (1/2 : ℝ) * bilin L (p+q) (p+q) =
    (1/2 : ℝ) * bilin L p p + (1/2 : ℝ) * bilin L q q + bilin L p q
  simp only [bilin_add_left, bilin_add_right]
  rw [bilin_symm L hL q p]
  ring

lemma qf_sub (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L (p-q) = QF L p + QF L q - bilin L p q := by
  change (1/2 : ℝ) * bilin L (p-q) (p-q) =
    (1/2 : ℝ) * bilin L p p + (1/2 : ℝ) * bilin L q q - bilin L p q
  simp only [bilin_sub_left, bilin_sub_right]
  rw [bilin_symm L hL q p]
  ring

lemma qf_smul (L : Matrix V V ℝ) (a : ℝ) (p : V → ℝ) :
    QF L (a • p) = a^2 * QF L p := by
  change (1/2 : ℝ) * bilin L (a • p) (a • p) = a^2 * ((1/2 : ℝ) * bilin L p p)
  rw [bilin_smul_left, bilin_smul_right]
  ring

lemma qf_exchange (L : Matrix V V ℝ) (hL : L.IsSymm)
    (x y d : V → ℝ) (a : ℝ) :
    QF L (x-a • d) + QF L (y+a • d) =
      QF L x + QF L y - a * bilin L (x-y) d + a^2 * bilin L d d := by
  simp only [qf_sub L hL, qf_add L hL, qf_smul, bilin_smul_right, bilin_sub_left]
  change (QF L x + a^2 * ((1/2 : ℝ) * bilin L d d) - a * bilin L x d) +
      (QF L y + a^2 * ((1/2 : ℝ) * bilin L d d) + a * bilin L y d) = _
  ring

lemma qf_parallelogram (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L p + QF L q = (1/2 : ℝ) * (QF L (p+q) + QF L (p-q)) := by
  rw [qf_add L hL, qf_sub L hL]
  ring

lemma row_minimum_formula (L : Matrix V V ℝ) (p : V → ℝ) (m : ℝ) (i : V) :
    L.mulVec p i = m * rowSum L i + ∑ j, L i j * (p j-m) := by
  change (∑ j, L i j * p j) = m * (∑ j, L i j) + ∑ j, L i j * (p j-m)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma row_square_sum (L : Matrix V V ℝ) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p i)^2) = ∑ i, rowSum L i * (p i)^2 := by
  simp only [rowSum, Finset.sum_mul]

lemma column_square_sum (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p j)^2) = ∑ i, rowSum L i * (p i)^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [hL.apply i]
  simp only [rowSum, Finset.sum_mul]

lemma edge_energy_identity (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p i-p j)^2) =
      2 * (∑ i, rowSum L i * (p i)^2) - 2 * bilin L p p := by
  calc
    (∑ i, ∑ j, L i j * (p i-p j)^2) =
        (∑ i, ∑ j, L i j * (p i)^2) + (∑ i, ∑ j, L i j * (p j)^2) -
          2 * (∑ i, ∑ j, L i j * (p i*p j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 2 * (∑ i, rowSum L i * (p i)^2) - 2 * bilin L p p := by
      rw [row_square_sum, column_square_sum L hL, ← bilin_eq_sum]
      ring

lemma energy_decomposition (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    QF L p = (1/2 : ℝ) * (∑ i, rowSum L i * (p i)^2) -
      (1/4 : ℝ) * (∑ i, ∑ j, L i j * (p i-p j)^2) := by
  have h := edge_energy_identity L hL p
  change (1/2 : ℝ) * bilin L p p = _
  linarith

lemma charVec_eq_single (i : V) : CharVec i = Pi.single i (1 : ℝ) := by
  ext j
  by_cases h : j=i <;> simp [CharVec,Pi.single_apply,h]

lemma dot_charVec_left (i : V) (p : V → ℝ) : dotProduct (CharVec i) p = p i := by
  simp [charVec_eq_single]

lemma dot_charVec_right (p : V → ℝ) (i : V) : dotProduct p (CharVec i) = p i := by
  simp [charVec_eq_single]

lemma mulVec_charVec (L : Matrix V V ℝ) (i j : V) :
    L.mulVec (CharVec j) i = L i j := by
  simp [charVec_eq_single, Matrix.mulVec_single_one]

lemma bilin_charVec_left (L : Matrix V V ℝ) (i : V) (p : V → ℝ) :
    bilin L (CharVec i) p = L.mulVec p i := by
  exact dot_charVec_left i _

lemma bilin_charVec_charVec (L : Matrix V V ℝ) (i j : V) :
    bilin L (CharVec i) (CharVec j) = L i j := by
  rw [bilin_charVec_left, mulVec_charVec]

lemma qf_charVec (L : Matrix V V ℝ) (i : V) : QF L (CharVec i) = (1/2 : ℝ) * L i i := by
  change (1/2 : ℝ) * bilin L (CharVec i) (CharVec i) = _
  rw [bilin_charVec_charVec]

lemma bilin_one_charVec (L : Matrix V V ℝ) (hL : L.IsSymm) (i : V) :
    bilin L (fun _ => (1 : ℝ)) (CharVec i) = rowSum L i := by
  rw [bilin_symm L hL, bilin_charVec_left]
  simp [Matrix.mulVec,dotProduct,rowSum]

lemma matrix_eq_of_qf_eq (L M : Matrix V V ℝ) (hL : L.IsSymm) (hM : M.IsSymm)
    (h : ∀ p : V → ℝ, QF L p = QF M p) : L = M := by
  ext i j
  have hi := h (CharVec i)
  have hj := h (CharVec j)
  have hij := h (CharVec i + CharVec j)
  rw [qf_add L hL, qf_add M hM, bilin_charVec_charVec, bilin_charVec_charVec] at hij
  linarith

#print axioms qf_exchange
#print axioms energy_decomposition
#print axioms matrix_eq_of_qf_eq

end QuadraticTranslationCore
end

/- Owned component: Solutions/QuadraticSubmodular.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace QuadraticTranslationOrder
open DiscreteConvex.CombinatorialB QuadraticTranslationCore

noncomputable def reflection (a t : ℝ) : ℝ := |t-a|-a

lemma reflection_lipschitz (a s t : ℝ) :
    |reflection a s-reflection a t| ≤ |s-t| := by
  have h := abs_abs_sub_abs_le_abs_sub (s-a) (t-a)
  have hleft : reflection a s-reflection a t = |s-a|-|t-a| := by
    unfold reflection
    ring
  have hright : (s-a)-(t-a)=s-t := by ring
  rw [hleft]
  simpa only [hright] using h

lemma reflection_zero (a : ℝ) (ha : 0 ≤ a) : reflection a 0 = 0 := by
  simp [reflection,abs_of_nonneg ha]

lemma reflection_square (a s : ℝ) (ha : 0 ≤ a) : (reflection a s)^2 ≤ s^2 := by
  apply sq_le_sq.mpr
  have h := reflection_lipschitz a s 0
  simpa only [reflection_zero a ha,sub_zero] using h

lemma reflection_edge_square (a s t : ℝ) :
    (reflection a s-reflection a t)^2 ≤ (s-t)^2 :=
  sq_le_sq.mpr (reflection_lipschitz a s t)

lemma shifted_max_min (p q a : ℝ) :
    max (p-a) q + min p (q+a) = p+q ∧
    max (p-a) q - min p (q+a) = reflection a (p-q) := by
  by_cases h : p-q ≤ a
  · have h1 : p-a ≤ q := by linarith
    have h2 : p ≤ q+a := by linarith
    rw [max_eq_right h1,min_eq_left h2]
    constructor
    · ring
    · unfold reflection
      rw [abs_of_nonpos (by linarith : p-q-a ≤ 0)]
      ring
  · have h1 : q ≤ p-a := by linarith
    have h2 : q+a ≤ p := by linarith
    rw [max_eq_left h1,min_eq_right h2]
    constructor
    · ring
    · unfold reflection
      rw [abs_of_nonneg (by linarith : 0 ≤ p-q-a)]
      ring

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def upperShift (p q : V → ℝ) (a : ℝ) : V → ℝ :=
  (p-a • (fun _ => (1 : ℝ))) ⊔ q

noncomputable def lowerShift (p q : V → ℝ) (a : ℝ) : V → ℝ :=
  p ⊓ (q+a • (fun _ => (1 : ℝ)))

lemma shifted_pair_shape (p q : V → ℝ) (a : ℝ) :
    upperShift p q a + lowerShift p q a = p+q ∧
    ∀ i, (upperShift p q a-lowerShift p q a) i = reflection a ((p-q) i) := by
  constructor
  · ext i
    simpa [upperShift,lowerShift,Pi.sup_apply,Pi.inf_apply,smul_eq_mul] using
      (shifted_max_min (p i) (q i) a).1
  · intro i
    simpa [upperShift,lowerShift,Pi.sup_apply,Pi.inf_apply,smul_eq_mul] using
      (shifted_max_min (p i) (q i) a).2

lemma energy_mono (L : Matrix V V ℝ) (hL : L.IsSymm) (ho : OffDiagNonpos L)
    (p q : V → ℝ)
    (hrow : (∑ i, rowSum L i * (p i)^2) ≤ ∑ i, rowSum L i * (q i)^2)
    (hedge : ∀ i j, (p i-p j)^2 ≤ (q i-q j)^2) : QF L p ≤ QF L q := by
  have hsum : (∑ i, ∑ j, L i j * (q i-q j)^2) ≤ ∑ i, ∑ j, L i j * (p i-p j)^2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i=j
    · subst j
      simp
    · exact mul_le_mul_of_nonpos_left (hedge i j) (ho i j hij)
  rw [energy_decomposition L hL,energy_decomposition L hL]
  linarith

lemma pair_energy_mono (L : Matrix V V ℝ) (hL : L.IsSymm) (ho : OffDiagNonpos L)
    (p q u v : V → ℝ) (hsum : u+v=p+q)
    (hrow : (∑ i, rowSum L i * ((u-v) i)^2) ≤ ∑ i, rowSum L i * ((p-q) i)^2)
    (hedge : ∀ i j, ((u-v) i-(u-v) j)^2 ≤ ((p-q) i-(p-q) j)^2) :
    QF L u + QF L v ≤ QF L p + QF L q := by
  have h := energy_mono L hL ho (u-v) (p-q) hrow hedge
  rw [qf_parallelogram L hL u v,qf_parallelogram L hL p q,hsum]
  linarith

lemma qf_nonneg_of_sign (L : Matrix V V ℝ) (hL : L.IsSymm)
    (ho : OffDiagNonpos L) (hr : DiagDominance L) (p : V → ℝ) : 0 ≤ QF L p := by
  have hrow : 0 ≤ ∑ i, rowSum L i * (p i)^2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hr i) (sq_nonneg _)
  have hedge : (∑ i, ∑ j, L i j * (p i-p j)^2) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    apply Finset.sum_nonpos
    intro j hj
    by_cases hij : i=j
    · subst j
      simp
    · exact mul_nonpos_of_nonpos_of_nonneg (ho i j hij) (sq_nonneg _)
  rw [energy_decomposition L hL]
  linarith

theorem posSemidef_of_sign (L : Matrix V V ℝ) (hL : L.IsSymm)
    (ho : OffDiagNonpos L) (hr : DiagDominance L) : L.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr hL)
  intro p
  have h := qf_nonneg_of_sign L hL ho hr p
  simp only [star_trivial]
  unfold QF at h
  linarith

theorem submodular_of_offdiag (L : Matrix V V ℝ) (hL : L.IsSymm)
    (ho : OffDiagNonpos L) : Submodular (QF L) := by
  intro p q
  obtain ⟨hsum,hdiff⟩ := shifted_pair_shape p q 0
  have hrow : (∑ i, rowSum L i * ((upperShift p q 0-lowerShift p q 0) i)^2) ≤
      ∑ i, rowSum L i * ((p-q) i)^2 := by
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiff i]
    simp [reflection]
  have hedge (i j : V) :
      ((upperShift p q 0-lowerShift p q 0) i-(upperShift p q 0-lowerShift p q 0) j)^2 ≤
        ((p-q) i-(p-q) j)^2 := by
    rw [hdiff i,hdiff j]
    exact reflection_edge_square 0 _ _
  have h := pair_energy_mono L hL ho p q _ _ hsum hrow hedge
  simpa only [upperShift,lowerShift,zero_smul,sub_zero,add_zero] using h

lemma charVec_sup_inf (i j : V) (hij : i ≠ j) :
    CharVec i ⊔ CharVec j = CharVec i+CharVec j ∧
    CharVec i ⊓ CharVec j = (0 : V → ℝ) := by
  constructor <;> ext k <;>
    by_cases hki : k=i <;> by_cases hkj : k=j <;>
      simp_all [CharVec,Pi.sup_apply,Pi.inf_apply,Pi.add_apply]

theorem offdiag_of_submodular (L : Matrix V V ℝ) (hL : L.IsSymm)
    (h : Submodular (QF L)) : OffDiagNonpos L := by
  intro i j hij
  obtain ⟨hsup,hinf⟩ := charVec_sup_inf i j hij
  have hh := h (CharVec i) (CharVec j)
  rw [hsup,hinf,qf_zero,qf_add L hL,bilin_charVec_charVec] at hh
  linarith

theorem offdiag_iff_submodular (L : Matrix V V ℝ) (hL : L.IsSymm) :
    OffDiagNonpos L ↔ Submodular (QF L) :=
  ⟨submodular_of_offdiag L hL,offdiag_of_submodular L hL⟩

theorem translation_of_sign (L : Matrix V V ℝ) (hL : L.IsSymm)
    (ho : OffDiagNonpos L) (hr : DiagDominance L) : TranslationSubmodular (QF L) := by
  intro p q a ha
  obtain ⟨hsum,hdiff⟩ := shifted_pair_shape p q a
  have hrow : (∑ i, rowSum L i * ((upperShift p q a-lowerShift p q a) i)^2) ≤
      ∑ i, rowSum L i * ((p-q) i)^2 := by
    apply Finset.sum_le_sum
    intro i hi
    rw [hdiff i]
    exact mul_le_mul_of_nonneg_left (reflection_square a _ ha) (hr i)
  have hedge (i j : V) :
      ((upperShift p q a-lowerShift p q a) i-(upperShift p q a-lowerShift p q a) j)^2 ≤
        ((p-q) i-(p-q) j)^2 := by
    rw [hdiff i,hdiff j]
    exact reflection_edge_square a _ _
  exact pair_energy_mono L hL ho p q _ _ hsum hrow hedge

lemma submodular_of_translation (g : (V → ℝ) → ℝ) (h : TranslationSubmodular g) :
    Submodular g := by
  intro p q
  simpa only [zero_smul,sub_zero,add_zero] using h p q 0 (le_refl 0)

lemma sign_of_translation (L : Matrix V V ℝ) (hL : L.IsSymm)
    (h : TranslationSubmodular (QF L)) : OffDiagNonpos L ∧ DiagDominance L := by
  refine ⟨offdiag_of_submodular L hL (submodular_of_translation _ h),?_⟩
  intro i
  let oneV : V → ℝ := fun _ => 1
  have hu : upperShift (oneV+CharVec i) 0 1 = CharVec i := by
    ext j
    by_cases hji : j=i <;>
      simp [upperShift,oneV,CharVec,hji,Pi.sup_apply]
  have hv : lowerShift (oneV+CharVec i) 0 1 = oneV := by
    ext j
    by_cases hji : j=i <;>
      simp [lowerShift,oneV,CharVec,hji,Pi.inf_apply]
  have hh := h (oneV+CharVec i) 0 1 (by norm_num)
  change QF L (oneV+CharVec i) + QF L 0 ≥
    QF L (upperShift (oneV+CharVec i) 0 1) + QF L (lowerShift (oneV+CharVec i) 0 1) at hh
  rw [hu,hv,qf_zero,qf_add L hL,bilin_one_charVec L hL] at hh
  change 0 ≤ rowSum L i
  linarith

theorem sign_iff_translation (L : Matrix V V ℝ) (hL : L.IsSymm) :
    (OffDiagNonpos L ∧ DiagDominance L) ↔ TranslationSubmodular (QF L) := by
  constructor
  · rintro ⟨ho,hr⟩
    exact translation_of_sign L hL ho hr
  · exact sign_of_translation L hL

#print axioms posSemidef_of_sign
#print axioms offdiag_iff_submodular
#print axioms sign_iff_translation

end QuadraticTranslationOrder
end

section
open DiscreteConvex.CombinatorialB

theorem solution {V : Type*} [Fintype V]
    [DecidableEq V] (L : Matrix V V ℝ) (hsymm : L.IsSymm) :
    (OffDiagNonpos L ∧ DiagDominance L) ↔ TranslationSubmodular (QF L) := by
  exact QuadraticTranslationOrder.sign_iff_translation L hsymm


#print axioms solution
end
