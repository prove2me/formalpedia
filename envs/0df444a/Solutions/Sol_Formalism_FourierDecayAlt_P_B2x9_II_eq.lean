-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.II_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:36:31.125923+00:00
-- url     : https://prove2.me/submissions/74bc69fa-6a79-48ae-9059-264cad72f39b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_tau_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_wt_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Ff_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_inner_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f) :
    II μG₁ f = ∫⁻ p, Ff (muP μG₁) f (tau k r' p) ∂(mCone k r') := by
  haveI := sigmaFinite_of_haar h₁
  haveI : SigmaFinite (muP μG₁) := sigmaFinite_of_haar hμP
  have hm : Measurable fun p : ℂ × HPar k r' => Ff (muP μG₁) f (tau k r' p) := (Ff_meas _ hf).comp tau_meas
  unfold II mCone
  rw [lintegral_prod (fun p => Ff (muP μG₁) f (tau k r' p)) hm.aemeasurable]
  unfold mC
  rw [lintegral_withDensity_eq_lintegral_mul _ wt_meas hm.lintegral_prod_right']
  refine lintegral_congr (fun c => ?_)
  simp only [Pi.mul_apply]
  rw [inner_eq HIv hG HI μG₁ h₁ hP hμP f hf c]
end Formalism.FourierDecayAlt.P.B2x9
