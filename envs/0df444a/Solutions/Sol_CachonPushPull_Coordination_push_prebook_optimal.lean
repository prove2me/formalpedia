-- Prove2me | solution 1 for CachonPushPull.Coordination.push_prebook_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:16:53.130069+00:00
-- url     : https://prove2.me/submissions/c613bec8-8778-4957-9b7b-05ce4076a972

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

theorem aux_ppo_exists (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ cdf μ q = t := by
  have hlim := tendsto_cdf_atTop μ
  have hev : ∀ᶠ x in Filter.atTop, t < cdf μ x := hlim.eventually (lt_mem_nhds ht1)
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1 hev
  have hMt : t < cdf μ (max M0 0) := hM0 (max M0 0) (le_max_left _ _)
  have hM0' : (0 : ℝ) ≤ max M0 0 := le_max_right _ _
  have hcont : ContinuousOn (cdf μ) (Set.Icc 0 (max M0 0)) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      exact ((cdf μ).right_continuous 0).mono Set.Icc_subset_Ici_self
    · exact (hD.hasDerivAt x h).continuousAt.continuousWithinAt
  have hivt := intermediate_value_Icc hM0' hcont
  have hmem : t ∈ Set.Icc (cdf μ 0) (cdf μ (max M0 0)) := by
    rw [hD.cdf_zero]; exact ⟨ht0, hMt.le⟩
  obtain ⟨q, hq, hqt⟩ := hivt hmem
  exact ⟨q, hq.1, hqt⟩

theorem aux_ppo_diff (μ : Measure ℝ) [IsProbabilityMeasure μ] (p v w q y : ℝ)
    (hq : cdf μ q = (p - w) / (p - v)) (hpv : v < p) :
    ((p - v) * S μ q - (w - v) * q) - ((p - v) * S μ y - (w - v) * y)
      = (p - v) * ∫ x in y..q, (cdf μ q - cdf μ x) := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  have hi : ∀ a b : ℝ, IntervalIntegrable (cdf μ) MeasureTheory.volume a b :=
    fun a b => hmono.intervalIntegrable
  unfold S
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hi y q),
    intervalIntegral.integral_const]
  have hsplit : (∫ x in (0:ℝ)..q, cdf μ x) - (∫ x in (0:ℝ)..y, cdf μ x)
      = ∫ x in y..q, cdf μ x :=
    intervalIntegral.integral_interval_sub_left (hi 0 q) (hi 0 y)
  have hpv' : p - v ≠ 0 := sub_ne_zero.2 (ne_of_gt hpv)
  have hF : (p - v) * cdf μ q = p - w := by rw [hq]; field_simp
  simp only [smul_eq_mul]
  linear_combination (-(p - v)) * hsplit - (q - y) * hF

theorem aux_ppo_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q y : ℝ) (hq0 : 0 ≤ q) (hy0 : 0 ≤ y) (hyq : y ≠ q) :
    0 < ∫ x in y..q, (cdf μ q - cdf μ x) := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  have hi : ∀ a b : ℝ, IntervalIntegrable (cdf μ) MeasureTheory.volume a b :=
    fun a b => hmono.intervalIntegrable
  rcases lt_or_gt_of_ne hyq with hlt | hlt
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact intervalIntegrable_const.sub (hi y q)
    · intro x hx
      have : cdf μ x < cdf μ q :=
        hD.strictMonoOn (Set.mem_Ici.2 (by linarith [hx.1])) (Set.mem_Ici.2 hq0) hx.2
      linarith
    · exact hlt
  · rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (intervalIntegrable_const.sub (hi q y)).neg
    · intro x hx
      have : cdf μ q < cdf μ x :=
        hD.strictMonoOn (Set.mem_Ici.2 hq0) (Set.mem_Ici.2 (by linarith [hx.1])) hx.1
      linarith
    · exact hlt

end CachonPushPull.Coordination

open CachonPushPull.Coordination
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w : ℝ) (hvw : v < w) (hwp : w ≤ p) :
    (∃ q : ℝ, 0 ≤ q ∧ cdf μ q = (p - w) / (p - v)) ∧
    ∀ q : ℝ, 0 ≤ q → cdf μ q = (p - w) / (p - v) →
      ∀ y : ℝ, 0 ≤ y → y ≠ q →
        (p - v) * S μ y - (w - v) * y < (p - v) * S μ q - (w - v) * q := by
  have hpv : v < p := lt_trans hvc hcp
  refine ⟨aux_ppo_exists μ f hD _ ?_ ?_, ?_⟩
  · apply div_nonneg <;> linarith
  · rw [div_lt_one (by linarith)]; linarith
  · intro q hq0 hq y hy0 hyq
    have hd := aux_ppo_diff μ p v w q y hq hpv
    have hpos := aux_ppo_pos μ f hD q y hq0 hy0 hyq
    have := mul_pos (sub_pos.2 hpv) hpos
    linarith
