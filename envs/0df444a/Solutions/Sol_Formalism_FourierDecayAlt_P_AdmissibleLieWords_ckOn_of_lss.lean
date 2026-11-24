-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ckOn_of_lss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:01:20.247829+00:00
-- url     : https://prove2.me/submissions/152c422e-ddf3-49cf-9611-4d2511c8516d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DminStarPd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutoffIteratedFDerivBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} {S : Set (Mat k r)}
    (h : LSS f S) (m : ℕ∞) : CkOn m S f := by
  intro g hg
  obtain ⟨f', hf', V, hV, hgV, hfe⟩ := h g hg
  refine ⟨V, f', hV, hgV, (hf'.of_le ?_).contDiffOn, fun g' hg' hG => hfe g' hG hg'⟩
  exact WithTop.coe_le_coe.mpr le_top
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
