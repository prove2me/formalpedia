-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.continuous_integral_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:25.02649+00:00
-- url     : https://prove2.me/submissions/b80516be-942f-4509-8df1-010d5853c3fc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_norm_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_continuous_psi

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
theorem _root_.solution (β : ℂ) (f : ℂ → E) (hf : Integrable f) :
    Continuous (fun w => ∫ z, G.psi β (w * z) • f z) := by
  refine continuous_of_dominated (bound := fun z => ‖f z‖) (fun w => ?_) (fun w => ?_) hf.norm ?_
  · exact (((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable).smul hf.1
  · exact Eventually.of_forall fun z => by rw [norm_smul, norm_psi, one_mul]
  · exact Eventually.of_forall fun z =>
      ((continuous_psi β).comp (continuous_id.mul continuous_const)).smul continuous_const
end Formalism.FourierDecayAlt.P.PBK
