-- Prove2me | solution 1 for BookProof.FriedrichsExtension.friedrichs_hypothesis_holds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:41:00.715945+00:00
-- url     : https://prove2.me/submissions/571a9003-04b9-44ac-8bc5-89491a928e48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFriedrichsExtension.lean — solution of BookProof.FriedrichsExtension.friedrichs_hypothesis_holds
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists
open BookProof.FriedrichsExtension




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ (D' : Submodule ℂ F) (H' : D' →ₗ[ℂ] F), Dense (D' : Set F) →
      SymmetricOn D' H' → (∀ x : D', 0 ≤ quadForm H' x) →
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension H' A :=
  fun D' H' hdense hsym hpos =>
      friedrichs_extension_exists ⟨D', H', hsym, hpos⟩ hdense
