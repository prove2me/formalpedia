-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.ckOn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:30:10.901859+00:00
-- url     : https://prove2.me/submissions/aed8917b-0f89-429a-8d4f-74557f97a525

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {f f₂ : Mat k r → E} {m : ℕ∞} (hf : CkOn m (GV k r) f) (hf₂ : CkOn m (GV k r) f₂) :
    CkOn m (GV k r) (f + f₂) := by
  unfold CkOn at *
  intro g₀ hg
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := hf g₀ hg
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := hf₂ g₀ hg
  refine ⟨U₁ ∩ U₂, f₁' + f₂', hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc₁.mono Set.inter_subset_left).add (hc₂.mono Set.inter_subset_right), ?_⟩
  intro g hgU hgG
  simp only [Pi.add_apply]
  rw [he₁ g hgU.1 hgG, he₂ g hgU.2 hgG]
end Formalism.FourierDecayAlt.P.B4
