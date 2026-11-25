-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_integral_psi_moving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:28.720547+00:00
-- url     : https://prove2.me/submissions/ed451e54-5648-4fe4-82cf-88cd74bd23dd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_integral_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_norm_integral_psi_sub_le

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
theorem _root_.solution {α : Type} {l : Filter α} (β : ℂ) (hβ : β ≠ 0) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (hw : Tendsto w l (cocompact ℂ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 0) := by
  have h0 := (tendsto_integral_psi β hβ f0).comp hw
  rw [← add_zero (0 : E)]
  have hsplit : ∀ᶠ x in l, ∫ z, G.psi β (w x * z) • f x z =
      ((∫ z, G.psi β (w x * z) • f x z) - ∫ z, G.psi β (w x * z) • f0 z) +
        ∫ z, G.psi β (w x * z) • f0 z := by
    filter_upwards with x
    abel
  refine Tendsto.congr' (EventuallyEq.symm hsplit) (Tendsto.add ?_ h0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hf
  filter_upwards [hfi] with x hx
  exact norm_integral_psi_sub_le β (w x) (f x) f0 hx hf0
end Formalism.FourierDecayAlt.P.PBK
