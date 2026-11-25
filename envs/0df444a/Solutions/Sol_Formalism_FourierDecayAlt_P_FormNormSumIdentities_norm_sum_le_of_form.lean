-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sum_le_of_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:47.041132+00:00
-- url     : https://prove2.me/submissions/321e91ff-2d2a-4e5a-b4fd-08f58c0cc223

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormNormSumIdentities_norm_sq_sum_eq_form

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
theorem _root_.solution {W : Type*} [SeminormedAddCommGroup W] [Module ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hB : ∀ x, (B x x).re ≤ (Cp * ‖x‖) ^ 2) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → W)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ Cp * ‖∑ j ∈ J, conj (a j) • y j‖ := by
  have h := norm_sq_sum_eq_form k v hv B J a P y hy
  have h2 := hB (∑ j ∈ J, conj (a j) • y j)
  rw [← h] at h2
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2 |> fun h3 => by
    simpa [abs_of_nonneg (norm_nonneg _)] using (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
end Formalism.FourierDecayAlt.P.FormNormSumIdentities
