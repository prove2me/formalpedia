-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_integral_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:27.236712+00:00
-- url     : https://prove2.me/submissions/ffe65bb4-6f16-44e0-996c-bd7d8ba61821

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_psi_eq_fourierChar
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_freq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (β : ℂ) (hβ : β ≠ 0) (f : ℂ → E) :
    Tendsto (fun w => ∫ z, G.psi β (w * z) • f z) (cocompact ℂ) (𝓝 0) := by
  have RL := (tendsto_integral_exp_inner_smul_cocompact f).comp (tendsto_freq β hβ)
  refine RL.congr fun w => ?_
  simp only [Function.comp_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [psi_eq_fourierChar, Circle.smul_def]
end Formalism.FourierDecayAlt.P.PBK
