-- Prove2me | solution 1 for Formalism.FN.partialBoxVolumeScaling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:41.243446+00:00
-- url     : https://prove2.me/submissions/99125606-e118-40dd-9148-bb3f20e05f83

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale
import Theorems.Thm_Formalism_FN_GjScaling_tm_mono
import Theorems.Thm_Formalism_FN_GjScaling_tm_empty
import Theorems.Thm_Formalism_FN_GjScaling_tm_add_singleton
import Theorems.Thm_Formalism_FN_GjScaling_lintegral_scale
import Theorems.Thm_Formalism_FN_GjScaling_continuous_emb_left
import Theorems.Thm_Formalism_FN_GjScaling_Gj_eq
import Theorems.Thm_Formalism_FN_GjScaling_card_compl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
namespace Formalism.FN
namespace GjScaling
variable {ι : Type*} [Fintype ι]
section decomp
variable (n j : ℕ)
private theorem torusImageVolume_fib_le_smul {D : Set (Fin n → ℝ)} (hDo : IsOpen D)
    (hDc : Convex ℝ D) {s : ℝ} (hs : 1 ≤ s) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    tm (fib n j D y) ≤ tm (fib n j (s • D) (s • y)) := by
  have hs0 : s ≠ 0 := (lt_of_lt_of_le one_pos hs).ne'
  rcases (fib n j D y).eq_empty_or_nonempty with h | ⟨w, hw⟩
  · rw [h, tm_empty]
    exact zero_le
  have hopen : IsOpen (fib n j D y) := hDo.preimage (continuous_emb_left n j y)
  rw [← tm_add_singleton hopen ((s - 1) • w)]
  apply tm_mono
  rintro _ ⟨u, hu, c, hc, rfl⟩
  rw [Set.mem_singleton_iff] at hc
  subst hc
  have hu' : emb n j u y ∈ D := hu
  have hw' : emb n j w y ∈ D := hw
  show emb n j (u + (s - 1) • w) (s • y) ∈ s • D
  rw [Set.mem_smul_set]
  refine ⟨s⁻¹ • emb n j u y + (1 - s⁻¹) • emb n j w y,
    hDc hu' hw' (inv_nonneg.2 (by linarith)) ?_ (by ring), ?_⟩
  · nlinarith [mul_nonneg (inv_nonneg.2 (zero_le_one.trans hs)) (sub_nonneg.2 hs),
      inv_mul_cancel₀ hs0]
  · have hinv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    funext i
    by_cases hi : (i : ℕ) < j
    · simp only [emb, dif_pos hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (u ⟨i, hi⟩ - w ⟨i, hi⟩) * hinv
    · simp only [emb, dif_neg hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
end decomp
end GjScaling
end Formalism.FN
end
end

set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open GjScaling
namespace Formalism.FN
theorem _root_.solution : GjScale := by
  intro n j C t t' hj hCo hCc _ _ ht htt'
  have ht' : 0 < t' := lt_of_lt_of_le ht htt'
  have hs : 0 < t' / t := div_pos ht' ht
  have hs1 : 1 ≤ t' / t := (le_div_iff₀ ht).2 (by linarith)
  have hD : IsOpen (t • C) := hCo.smul₀ ht.ne'
  have hDc : Convex ℝ (t • C) := hCc.smul t
  have hsD : t' • C = (t' / t) • (t • C) := by
    rw [smul_smul, div_mul_eq_mul_div, mul_div_assoc, div_self ht.ne', mul_one]
  have key := Formalism.FN.GjScaling.lintegral_scale
    (fun y => Formalism.FN.GjScaling.tm (Formalism.FN.GjScaling.fib n j ((t' / t) • (t • C)) y)) hs
  beta_reduce at key
  rw [Formalism.FN.GjScaling.card_compl n j hj] at key
  rw [hsD, Formalism.FN.GjScaling.Gj_eq n j _ hD,
    Formalism.FN.GjScaling.Gj_eq n j _ (hD.smul₀ hs.ne'), key]
  exact mul_le_mul_of_nonneg_left
    (lintegral_mono fun y => _root_.Formalism.FN.GjScaling.torusImageVolume_fib_le_smul n j hD hDc hs1 y) (by positivity)
end Formalism.FN
