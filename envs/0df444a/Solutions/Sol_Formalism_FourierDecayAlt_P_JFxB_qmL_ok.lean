-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.qmL_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:08.383829+00:00
-- url     : https://prove2.me/submissions/2a38f6ba-12f8-4feb-b875-fdd96e55fa6a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_foldL_ok
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
theorem _root_.solution {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) : WOK (qmL k r p q u) t := by
  intro cw hcw
  simp only [qmL, List.mem_flatMap, List.mem_map] at hcw
  obtain ⟨σ, -, cw', hcw', rfl⟩ := hcw
  obtain ⟨h1, h2⟩ := foldL_ok (k := k) (r := r) (tsOf p q u σ) cw' hcw'
  exact ⟨h1, by simpa [tsOf] using h2⟩
end Formalism.FourierDecayAlt.P.JFxB
