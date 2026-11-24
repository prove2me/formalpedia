-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.inf_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:22:58.603611+00:00
-- url     : https://prove2.me/submissions/762ff9b5-4012-4ce3-b7fc-eace07d50d67

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_isOpen_Quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_ae_eq

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (hAe : AeFromTests) (hRB : RegBound D A) (hRA : RegAverage D A) (hU : Unfold D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∀ τ ∈ Quad, betaInfTau D τ F F = ((|(betaInfTau D τ F F).re| : ℝ) : ℂ) := by
  have hc := hRB.2.1 F F hF hF
  have hc' : ContinuousOn (fun τ => ((|(betaInfTau D τ F F).re| : ℝ) : ℂ)) Quad :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuous_abs.comp_continuousOn (Complex.continuous_re.comp_continuousOn hc))
  refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Quad hc hc'
  filter_upwards [ae_eq hAe hRB hRA hU hF] with τ h
  rw [← h.2]
  simp [abs_of_nonneg ENNReal.toReal_nonneg]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
