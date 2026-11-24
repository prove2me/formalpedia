-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Jv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:06:02.867451+00:00
-- url     : https://prove2.me/submissions/b83b80ef-a154-4ea5-9e19-cac6401d1f69

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity__Q_ac_6158466ce3b3
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_hsVec_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Jtau_add

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
theorem _root_.solution (hJ : JCont D A) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) (hF' : InCC A 4 F')
    (τ : ℝ × ℝ) : ∀ᵐ q ∂μQ D, Jv D τ (F + F') q = Jv D τ F q + Jv D τ F' q := by
  filter_upwards [(μQ_ac D).ae_le (hJ F hF).1, (μQ_ac D).ae_le (hJ F' hF').1] with q h h'
  unfold Jv
  rw [Jtau_add D τ h h', hsVec_add]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
