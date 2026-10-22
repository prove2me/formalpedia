-- Prove2me | solution 1 for FirstPriceLearning.Stochastic.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:39:14.399729+00:00
-- url     : https://prove2.me/submissions/5fed893a-4f91-47a3-8b76-564d31a3a1ad

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

set_option autoImplicit false
open MeasureTheory FirstPriceLearning.Stochastic

theorem solution (K : ℕ) (hK : 1 ≤ K) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    MonotoneOn (largestMaximizer μG (gridA K)) (Set.Icc 0 1) := by
  intro v1 _ v2 _ hv
  have hA : (gridA K).Nonempty := by
    unfold gridA
    rw [Finset.image_nonempty, Finset.nonempty_range_iff]
    omega
  have hGmono : Monotone (cdf μG) := by
    intro x y hxy
    unfold cdf
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.2 hxy))
  unfold largestMaximizer
  rw [dif_pos hA, dif_pos hA]
  apply Finset.max'_le
  intro y hy
  have hyA := (Finset.mem_filter.1 hy).1
  have hy1 := (Finset.mem_filter.1 hy).2
  by_contra hlt
  push_neg at hlt
  set M2 := (gridA K).filter (fun b => ∀ b' ∈ gridA K, expReward μG v2 b' ≤ expReward μG v2 b) with hM2
  have hne : M2.Nonempty := by
    obtain ⟨b, hb, hmax⟩ := (gridA K).exists_max_image (expReward μG v2) hA
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, hmax⟩⟩
  have hb2 := Finset.max'_mem M2 hne
  set b2 := M2.max' hne with hb2def
  have hb2A := (Finset.mem_filter.1 hb2).1
  have hb2m := (Finset.mem_filter.1 hb2).2
  have hdiff : expReward μG v2 b2 ≤ expReward μG v2 y := by
    have h1 := hy1 b2 hb2A
    have h2 := mul_nonneg (sub_nonneg.2 hv) (sub_nonneg.2 (hGmono hlt.le))
    unfold expReward at h1 ⊢
    nlinarith [h1, h2]
  have hyM2 : y ∈ M2 := by
    refine Finset.mem_filter.2 ⟨hyA, fun b' hb' => (hb2m b' hb').trans hdiff⟩
  have := Finset.le_max' M2 y hyM2
  exact absurd hlt (not_lt.2 this)
