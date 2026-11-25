-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.betaTau_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:36.77819+00:00
-- url     : https://prove2.me/submissions/2c6e56e6-26a0-476e-aa09-4211dac7404b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_normSqTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_betaTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Jv_aesm

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
theorem _root_.solution (hJ : JCont D A) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F)
    {τ : ℝ × ℝ} (hτ : τ ∈ Quad) : betaTau D τ F F = (((normSqTau D τ F).toReal : ℝ) : ℂ) := by
  rw [betaTau_eq, normSqTau_eq]
  have : (fun q => inner ℂ (Jv D τ F q) (Jv D τ F q)) = fun q => ((‖Jv D τ F q‖ ^ 2 : ℝ) : ℂ) := by
    funext q
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hm : AEStronglyMeasurable (fun q => ‖Jv D τ F q‖ ^ 2) (μQ D) := (Jv_aesm hJ hF hτ).norm.pow 2
  rw [this, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q => by positivity) hm]
  congr 3
  funext q
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
