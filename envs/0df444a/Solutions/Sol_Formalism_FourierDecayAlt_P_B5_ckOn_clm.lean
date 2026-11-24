-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.ckOn_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:06:15.845107+00:00
-- url     : https://prove2.me/submissions/237d7818-bc83-4000-9572-fd27c670f7c1

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {m : ℕ∞} {f : Mat k r → E}
    (h : CkOn m (GV k r) f) (L : E →L[ℂ] E') : CkOn m (GV k r) (fun g => L (f g)) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf', he⟩ := h g₀ hg₀
  refine ⟨U, fun x => L (f' x), hU, hg, ?_, fun g hgU hgG => by simp only [he g hgU hgG]⟩
  exact (L.restrictScalars ℝ).contDiff.comp_contDiffOn hf'
end Formalism.FourierDecayAlt.P.B5
