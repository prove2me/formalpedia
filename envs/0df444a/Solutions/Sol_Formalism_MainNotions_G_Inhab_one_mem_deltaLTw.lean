-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.one_mem_deltaLTw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:50.403802+00:00
-- url     : https://prove2.me/submissions/1eb10b0d-a76e-454f-86bc-c400cd3953e6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_weyl
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
    (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ deltaLTw R K m 0 g := by
  unfold deltaLTw
  refine Submodule.mem_map.mpr ⟨1, ?_, by simp⟩
  have hν : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
    funext t
    simp [nuOf]
  rw [hν]
  unfold deltaL
  rw [Submodule.mem_comap]
  simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, map_one]
  exact Submodule.mem_map.mpr ⟨1, one_mem_weyl R (m + 1), by simp⟩
end Formalism.MainNotions.G.Inhab
