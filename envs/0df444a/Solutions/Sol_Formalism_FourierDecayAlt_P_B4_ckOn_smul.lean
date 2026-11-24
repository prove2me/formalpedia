-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.ckOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:32:22.021808+00:00
-- url     : https://prove2.me/submissions/9c5efb76-ad25-4322-868c-2178fd08d3a7

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
theorem _root_.solution {f : Mat k r → E} {m : ℕ∞} (a : ℂ) (hf : CkOn m (GV k r) f) :
    CkOn m (GV k r) (a • f) := by
  unfold CkOn at *
  intro g₀ hg
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg
  refine ⟨U, a • f', hU, hgU, hc.const_smul a, ?_⟩
  intro g hgU' hgG
  simp only [Pi.smul_apply]
  rw [he g hgU' hgG]
end Formalism.FourierDecayAlt.P.B4
