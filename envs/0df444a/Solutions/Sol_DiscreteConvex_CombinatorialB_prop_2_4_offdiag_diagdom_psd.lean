-- Prove2me | solution 1 for DiscreteConvex.CombinatorialB.prop_2_4_offdiag_diagdom_psd
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T03:39:23.469534+00:00
-- url     : https://prove2.me/submissions/b849da64-a716-469a-9a2b-1ecef7848eb9

import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
import Definitions.Def_DiscreteConvex_CombinatorialB_DiagDominance
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped BigOperators

namespace QuadraticPositivityCore
open DiscreteConvex.CombinatorialB
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bilin (L : Matrix V V ℝ) (p q : V → ℝ) : ℝ :=
  dotProduct p (L.mulVec q)

noncomputable def rowSum (L : Matrix V V ℝ) (i : V) : ℝ := ∑ j, L i j

lemma bilin_eq_sum (L : Matrix V V ℝ) (p q : V → ℝ) :
    bilin L p q = ∑ i, ∑ j, L i j * (p i * q j) := by
  simp only [bilin, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
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

end QuadraticPositivityCore

namespace QuadraticPositivityOrder
open DiscreteConvex.CombinatorialB QuadraticPositivityCore



variable {V : Type*} [Fintype V] [DecidableEq V]

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

end QuadraticPositivityOrder

open DiscreteConvex.CombinatorialB

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (hsymm : L.IsSymm) (h9 : OffDiagNonpos L) (h10 : DiagDominance L) :
    L.PosSemidef := by
  exact QuadraticPositivityOrder.posSemidef_of_sign L hsymm h9 h10


#print axioms solution
