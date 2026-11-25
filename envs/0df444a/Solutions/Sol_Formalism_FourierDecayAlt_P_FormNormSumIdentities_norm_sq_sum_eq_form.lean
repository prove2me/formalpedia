-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sq_sum_eq_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:35.773653+00:00
-- url     : https://prove2.me/submissions/62720b7e-0ae5-4afe-9ef2-d42fe71d5fb8

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormNormSumIdentities_inner_sum_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormNormSumIdentities_form_sum_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FormNormSumIdentities
open Finset
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities
theorem _root_.solution (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → V)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = (B (∑ j ∈ J, conj (a j) • y j) (∑ j ∈ J, conj (a j) • y j)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sum_smul k v hv, form_sum_conj, RCLike.re_to_complex]
  congr 1
  refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
  rw [hy j hj l hl]
end Formalism.FourierDecayAlt.P.FormNormSumIdentities
