-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.norm_integral_psi_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:31.02533+00:00
-- url     : https://prove2.me/submissions/9e24b41e-2edb-48ab-8168-4dc796a86396

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
theorem _root_.solution (β w : ℂ) (f g : ℂ → E) (hf : Integrable f) (hg : Integrable g) :
    ‖(∫ z, G.psi β (w * z) • f z) - ∫ z, G.psi β (w * z) • g z‖ ≤ ∫ z, ‖f z - g z‖ := by
  have hfi : Integrable (fun z => G.psi β (w * z) • f z) :=
    hf.bdd_smul 1 ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_psi β _).le)
  have hgi : Integrable (fun z => G.psi β (w * z) • g z) :=
    hg.bdd_smul 1 ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_psi β _).le)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) (hf.sub hg).norm (Eventually.of_forall fun z => ?_))
  simp only [← smul_sub, norm_smul, norm_psi, one_mul, le_refl]
end Formalism.FourierDecayAlt.P.PBK
