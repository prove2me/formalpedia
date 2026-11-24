-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.unitL_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:58.143497+00:00
-- url     : https://prove2.me/submissions/a26c5117-2b7c-4e95-a64c-6f252808d9d5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_nrm_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j) :
    ∀ cw ∈ unitL L, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ j := by
  intro cw hcw
  simp only [unitL, List.mem_map] at hcw
  obtain ⟨cw', hcw', rfl⟩ := hcw
  obtain ⟨h1, h2⟩ := hL cw' hcw'
  refine ⟨?_, by simpa using h2⟩
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨Y, hY, rfl⟩ := hX
  exact nrm_unit (h1 Y hY)
end Formalism.FourierDecayAlt.P.JFxB
