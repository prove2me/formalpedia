-- Prove2me | solution 1 for DiscreteConvex.CombinatorialB.prop_2_6_offdiag_iff_submodular
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T04:08:50.261993+00:00
-- url     : https://prove2.me/submissions/cb5e92ce-9f57-46c9-9bc0-d89e8a6d7a6a

import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
import Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
import Definitions.Def_DiscreteConvex_CombinatorialB_Submodular
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped BigOperators

namespace QuadraticPlainCore
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

lemma qf_parallelogram (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L p + QF L q = (1/2 : ℝ) * (QF L (p+q) + QF L (p-q)) := by
  rw [qf_add L hL, qf_sub L hL]
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

lemma mulVec_charVec (L : Matrix V V ℝ) (i j : V) :
    L.mulVec (CharVec j) i = L i j := by
  simp [charVec_eq_single, Matrix.mulVec_single_one]

lemma bilin_charVec_left (L : Matrix V V ℝ) (i : V) (p : V → ℝ) :
    bilin L (CharVec i) p = L.mulVec p i := by
  exact dot_charVec_left i _

lemma bilin_charVec_charVec (L : Matrix V V ℝ) (i j : V) :
    bilin L (CharVec i) (CharVec j) = L i j := by
  rw [bilin_charVec_left, mulVec_charVec]

end QuadraticPlainCore

namespace QuadraticPlainOrder
open DiscreteConvex.CombinatorialB QuadraticPlainCore

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

end QuadraticPlainOrder

open DiscreteConvex.CombinatorialB

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (hsymm : L.IsSymm) :
    OffDiagNonpos L ↔ Submodular (QF L) := by
  exact QuadraticPlainOrder.offdiag_iff_submodular L hsymm

#print axioms QuadraticPlainOrder.offdiag_iff_submodular
#print axioms solution
