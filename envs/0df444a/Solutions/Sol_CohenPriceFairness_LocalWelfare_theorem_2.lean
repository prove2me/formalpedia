-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.theorem_2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:06:13.174197+00:00
-- url     : https://prove2.me/submissions/021d89a1-fcf0-4fb0-aadc-d8637467ff48

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory Filter Topology CohenPriceFairness.LocalWelfare

theorem solution : ¬ (∀ (m : Market) (hd : ∀ i, 0 < m.population i)
    (hc : 0 ≤ m.cost) (hf : Families m),
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 < D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 < D) ∧
      SensitivityClaim m b .demand (fun D => D < 0) ∧
      SensitivityClaim m b .surplus (fun D => D < 0)) := by
  intro H
  let m : Market := ⟨fun i => uniformLaw (![1, 2] i), fun _ => 1, 5⟩
  have hdem : ∀ i p, 5 ≤ p → demand m i p = 0 := by
    intro i p hp
    have hb : ![(1:ℝ), 2] i ≤ 2 := by fin_cases i <;> norm_num
    simp only [demand, m, uniformLaw, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply measurableSet_Ici]
    have : Set.Ici p ∩ Set.Icc 0 (![(1:ℝ), 2] i) = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and, not_le]
      intro h1 _; linarith
    rw [this]; simp
  have hprof : ∀ i p, profit m i p ≤ 0 := by
    intro i p
    by_cases hp : 5 ≤ p
    · simp [profit, hdem i p hp]
    · simp only [profit, m]
      have : 0 ≤ demand m i p := ENNReal.toReal_nonneg
      nlinarith
  have hb10 : BaselineOptimal m (fun _ => 10) := by
    intro i
    refine ⟨by norm_num, fun p _ => ?_⟩
    have : profit m i 10 = 0 := by simp [profit, hdem i 10 (by norm_num)]
    rw [this]; exact hprof i p
  have hfam : Families m := Or.inl ⟨![1, 2], by intro i; fin_cases i <;> norm_num, by norm_num,
    fun i => rfl⟩
  obtain ⟨-, h2⟩ := H m (fun _ => one_pos) (by norm_num [m]) hfam
  obtain ⟨⟨-, hP⟩, -⟩ := h2 _ hb10
  have hsel : LocalOptimalSelection m (fun _ => 10) .price (fun _ => fun _ => 10) := by
    refine ⟨rfl, 1, one_pos, le_rfl, fun α hα => ⟨⟨hα, fun _ => by norm_num, by simp [gap, metricValue]⟩, ?_⟩⟩
    intro q _
    have h0 : totalProfit m (fun _ => 10) = 0 := by
      simp [totalProfit, profit, hdem _ 10 (by norm_num)]
    rw [h0]
    have := hprof 0 (q 0); have := hprof 1 (q 1)
    simp only [totalProfit]; linarith
  obtain ⟨D, hD, hpos⟩ := hP _ hsel
  have h0 : Tendsto (fun α : ℝ => (welfare m (fun _ => 10) - welfare m (fun _ => 10)) / α)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simp only [sub_self, zero_div]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hD h0
  linarith
