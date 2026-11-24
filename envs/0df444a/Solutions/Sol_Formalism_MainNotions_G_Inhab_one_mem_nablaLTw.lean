-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.one_mem_nablaLTw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:40:12.707547+00:00
-- url     : https://prove2.me/submissions/4f8327a2-4e69-4dc1-bba3-3b67db6e45b8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_dualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_one_mem_dualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ nablaLTw R K m 0 g := by
  unfold nablaLTw
  refine Submodule.mem_map.mpr ⟨1, ?_, by simp⟩
  have hν : (fun t : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) t - (0 : Fin (m + 1) → ℤ) (Fin.last m)).toNat) = 0 := by
    funext t
    simp
  rw [hν]
  unfold nablaL
  rw [Submodule.mem_comap]
  simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, map_one]
  exact Submodule.mem_map.mpr ⟨1, one_mem_dualWeyl R (m + 1) (m + 1), by simp⟩
end Formalism.MainNotions.G.Inhab
