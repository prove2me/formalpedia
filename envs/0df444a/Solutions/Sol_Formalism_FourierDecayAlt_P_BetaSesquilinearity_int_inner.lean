-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.int_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:14:50.393013+00:00
-- url     : https://prove2.me/submissions/8228b99c-0ed3-4ead-81dc-99b7ffd21f66

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Jv_aesm
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Jv_memLp

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
theorem _root_.solution (hJ : JCont D A) (hDD : DiagDom D A) {F G : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F)
    (hG : InCC A 4 G) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) :
    Integrable (fun q => inner ℂ (Jv D τ G q) (Jv D τ F q)) (μQ D) := by
  have h : Integrable (fun q => ‖Jv D τ G q‖ * ‖Jv D τ F q‖) (μQ D) :=
    MemLp.integrable_mul (Jv_memLp hJ hDD hG hτ).norm (Jv_memLp hJ hDD hF hτ).norm
  exact h.mono' ((Jv_aesm hJ hG hτ).inner (Jv_aesm hJ hF hτ)) (Eventually.of_forall fun q => norm_inner_le_norm _ _)
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
