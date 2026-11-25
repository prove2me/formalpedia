-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.diagDom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:15.135626+00:00
-- url     : https://prove2.me/submissions/5f0b169e-ebc9-4105-a934-7dc2fe6d0544

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity__Q_ac_6158466ce3b3
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_normSqTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_hsVec_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_isOpen_Quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_ae_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_inf_abs
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
theorem _root_.solution (hAe : AeFromTests) (hFa : FatouParam) (hRB : RegBound D A) (hRA : RegAverage D A)
    (hU : Unfold D A) (hJ : JCont D A) : DiagDom D A := by
  intro F hF τ hτ
  have habs := inf_abs hAe hRB hRA hU hF
  refine ⟨by rw [habs τ hτ]; simp, ?_⟩
  rw [normSqTau_eq]
  refine hFa _ (μQ D) _ Quad (fun τ => Jv D τ F) (fun τ => (betaInfTau D τ F F).re) isOpen_Quad
    (fun τ hτ => Jv_aesm hJ hF hτ) ?_ ?_ ?_ τ hτ
  · have := (μQ_ac D).ae_le (hJ F hF).2.1
    filter_upwards [this] with q hq
    exact hsVec_cont.comp_continuousOn hq
  · exact Complex.continuous_re.comp_continuousOn (hRB.2.1 F F hF hF)
  · filter_upwards [ae_eq hAe hRB hRA hU hF] with τ h
    rw [← normSqTau_eq, ← h.2]
    simp [ENNReal.ofReal_toReal h.1]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
