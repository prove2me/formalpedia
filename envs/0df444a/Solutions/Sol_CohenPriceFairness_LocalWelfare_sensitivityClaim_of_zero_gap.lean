-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.sensitivityClaim_of_zero_gap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:35.977819+00:00
-- url     : https://prove2.me/submissions/abd56cd7-0d3c-4000-b36e-ec86335a18b2

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity

open CohenPriceFairness.LocalWelfare
open Filter Topology Set

theorem solution (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop)
    (hC : C 0) (hb : BaselineOptimal m b) (huniq : ∀ b' : Prices, BaselineOptimal m b' → b' = b)
    (hgap : metricValue m k 0 (b 0) = metricValue m k 1 (b 1)) :
    SensitivityClaim m b k C := by
  have hg : gap m k b = 0 := by unfold gap; rw [hgap, sub_self, abs_zero]
  have hbopt : ∀ α ∈ Set.Icc (0:ℝ) 1, FairOptimal m b k α b := by
    intro α hα
    refine ⟨⟨hα, fun i => (hb i).1, by rw [hg, mul_zero]⟩, fun q hq => ?_⟩
    unfold totalProfit
    exact add_le_add ((hb 0).2 _ (hq.2.1 0)) ((hb 1).2 _ (hq.2.1 1))
  refine ⟨⟨fun _ => b, rfl, 1, one_pos, le_rfl, hbopt⟩, ?_⟩
  rintro P ⟨hP0, ε, hε, hε1, hP⟩
  have hPb : ∀ α ∈ Set.Icc (0:ℝ) ε, P α = b := by
    intro α hα
    have hα1 : α ∈ Set.Icc (0:ℝ) 1 := ⟨hα.1, hα.2.trans hε1⟩
    obtain ⟨⟨_, hnn, _⟩, hmax⟩ := hP α hα
    have hge := hmax b (hbopt α hα1).1
    unfold totalProfit at hge
    have h0 := (hb 0).2 _ (hnn 0)
    have h1 := (hb 1).2 _ (hnn 1)
    have key : ∀ i, profit m i (b i) ≤ profit m i (P α i) := by
      rw [Fin.forall_fin_two]; constructor <;> linarith
    exact huniq _ (fun i => ⟨hnn i, fun p hp => ((hb i).2 p hp).trans (key i)⟩)
  refine ⟨0, ?_, hC⟩
  unfold RightDerivative
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hε] with α hα
  rw [hPb α ⟨hα.1.le, hα.2.le⟩, hP0, sub_self, zero_div]

