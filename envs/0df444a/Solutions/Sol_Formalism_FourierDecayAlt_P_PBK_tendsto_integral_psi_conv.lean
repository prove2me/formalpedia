-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_integral_psi_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:17.178803+00:00
-- url     : https://prove2.me/submissions/0e546a6f-dcf4-466e-b219-57b998ab67dd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_norm_integral_psi_sub_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_continuous_integral_psi

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
theorem _root_.solution {α : Type} {l : Filter α} (β : ℂ) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (σ : ℂ) (hw : Tendsto w l (𝓝 σ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 (∫ z, G.psi β (σ * z) • f0 z)) := by
  have h0 := ((continuous_integral_psi β f0 hf0).tendsto σ).comp hw
  rw [← zero_add (∫ z, G.psi β (σ * z) • f0 z)]
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
