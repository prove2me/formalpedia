-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.rz_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:15:36.382833+00:00
-- url     : https://prove2.me/submissions/3c63babc-c166-4a16-8189-d59cb1d09ee5

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_Sup_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_rd_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.CapelliCoordinates
theorem _root_.solution {F : Mx k r → E} (hF : SmoothLev k r i D F) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    ∃ L : Mx k r →ₗ[ℂ] E, ∀ Z, Sup k r i Z → RZ (Hpk k r) Z F g = L Z := by
  obtain ⟨L, hL⟩ := rd_linear hF hg
  refine ⟨cx (Hpk k r) L, fun Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := hZ.lie
  show RdV (hpart1 (Hpk k r) Z) F g + Complex.I • RdV (hpart2 (Hpk k r) Z) F g = _
  rw [hL _ h1, hL _ h2]
  rfl
end Formalism.FourierDecayAlt.P.CapelliCoordinates
