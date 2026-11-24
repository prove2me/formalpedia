-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.actFormWedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:10:32.217632+00:00
-- url     : https://prove2.me/submissions/3db0d7b1-9def-45df-9e72-6be99b6c25a3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lap_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : FactX2wedge := by
  intro R _ n K X m
  funext J
  simp only [actF, wedgeF]
  have hR : ∑ b ∈ J, ((sg J b : ℤ) : R) * (∑ I', K I' * minorF m I' (J.erase b)) * Matrix.vecMul X m b =
      ∑ I', ∑ a, K I' * X a * ∑ b ∈ J, ((sg J b : ℤ) : R) * minorF m I' (J.erase b) * m a b := by
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hR]
  simp only [lap_row]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun a => Finset.univ.filter (fun I => a ∈ I))
    (by intro I a; simp)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hZ : ∑ I', K I' * X a * (if a ∈ I' then 0 else ((sg (insert a I') a : ℤ) : R) * minorF m (insert a I') J) =
      ∑ I' ∈ Finset.univ.filter (fun I' => a ∉ I'),
        K I' * X a * (((sg (insert a I') a : ℤ) : R) * minorF m (insert a I') J) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I' _
    split_ifs <;> simp_all
  rw [hZ]
  refine Finset.sum_nbij' (fun I => I.erase a) (fun I' => insert a I') ?_ ?_ ?_ ?_ ?_
  · intro I hI
    simp
  · intro I' hI'
    simp
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
    exact Finset.insert_erase hI
  · intro I' hI'
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hI'
    exact Finset.erase_insert hI'
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
    simp only [Finset.insert_erase hI]
    ring
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
