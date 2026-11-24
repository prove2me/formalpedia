-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_coaction_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:15.776379+00:00
-- url     : https://prove2.me/submissions/4ee22784-c331-4fa8-a76b-dbce8fe44304

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationCoactionStable
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_equiv_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : FiltrationCoactionStable := by
  intro n _ M CF pi _ x hx l
  let L0 : (M.ι → ℤ) →+ (M.ι → ℤ) :=
    { toFun := fun x i => l (∑ k, M.A i k * (x k : GLCoord ℤ n))
      map_zero' := by funext i; simp
      map_add' := fun x y => by
        funext i
        simp only [Pi.add_apply, Int.cast_add, mul_add, sum_add_distrib, map_add] }
  let L : (M.ι → ℤ) →ₗ[ℤ] (M.ι → ℤ) := L0.toIntLinearMap
  have hL : CF.Mpi pi ≤ (CF.Mpi pi).comap L := by
    unfold ColFam.Mpi
    rw [Submodule.span_le]
    rintro y ⟨j, hj, I, rfl⟩
    have : L (CF.vec j I) = ∑ K, l (TMat (CF.mu j) K I) • CF.vec j K := by
      funext i
      have h1 : L (CF.vec j I) i = l (∑ k, M.A i k * (CF.ph j k I : GLCoord ℤ n)) := rfl
      rw [h1, qb_equiv_apply, map_sum, Finset.sum_apply]
      refine sum_congr rfl fun K _ => ?_
      rw [← zsmul_eq_mul, map_zsmul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
    rw [SetLike.mem_coe, Submodule.mem_comap, this]
    exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, K, rfl⟩)
  exact hL hx
end Formalism.InvariantFactorPaths.ColumnFamilies
