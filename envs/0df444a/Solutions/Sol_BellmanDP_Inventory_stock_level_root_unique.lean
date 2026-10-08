-- Prove2me | solution 1 for BellmanDP.Inventory.stock_level_root_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:09:23.433319+00:00
-- url     : https://prove2.me/submissions/fa235fe8-477d-47b9-b154-e7e4bb66357a

import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology


namespace BellmanDP.Inventory

lemma dd_ii {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y : ℝ} (hy : 0 ≤ y) :
    IntervalIntegrable φ volume 0 y :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).2
    (hφ.integrable.mono_set Set.Ioc_subset_Ioi_self)

lemma dd_tail {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y : ℝ} (hy : 0 ≤ y) :
    ∫ s in Set.Ioi y, φ s = 1 - ∫ s in (0:ℝ)..y, φ s := by
  have h := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (0:ℝ)) (b := y)) measurableSet_Ioi
    (hφ.integrable.mono_set Set.Ioc_subset_Ioi_self) (hφ.integrable.mono_set (Set.Ioi_subset_Ioi hy))
  rw [Set.Ioc_union_Ioi_eq_Ioi hy, hφ.total] at h
  rw [intervalIntegral.integral_of_le hy]; linarith

lemma dd_strict {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y₁ y₂ : ℝ} (h1 : 0 ≤ y₁) (h12 : y₁ < y₂) :
    (∫ s in (0:ℝ)..y₁, φ s) < ∫ s in (0:ℝ)..y₂, φ s := by
  have hi1 := dd_ii hφ h1
  have hi2 := dd_ii hφ (h1.trans h12.le)
  have h := intervalIntegral.integral_add_adjacent_intervals hi1 (hi1.symm.trans hi2)
  have hpos : 0 < ∫ s in y₁..y₂, φ s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hi1.symm.trans hi2)
      (fun x hx => hφ.pos x (lt_of_le_of_lt h1 hx.1)) h12
  linarith

lemma root_iff (k p a : ℝ) (φ : ℝ → ℝ) (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p) {y : ℝ} (hy : 0 ≤ y) :
    StockLevelRoot k p a φ y ↔ (∫ s in (0 : ℝ)..y, φ s) = (a * p - k) / (a * (p - k)) := by
  have hpk : k < p := by nlinarith
  have hden : 0 < a * (p - k) := mul_pos ha0 (by linarith)
  unfold StockLevelRoot
  rw [dd_tail hφ hy, eq_div_iff hden.ne']
  constructor <;> intro h <;> linarith

theorem root_core (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p) :
    (∀ y : ℝ, 0 ≤ y →
      (StockLevelRoot k p a φ y ↔ (∫ s in (0 : ℝ)..y, φ s) = (a * p - k) / (a * (p - k)))) ∧
    ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
      ∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar := by
  refine ⟨fun y hy => root_iff k p a φ hk hp hφ ha0 ha1 hapk hy, ?_⟩
  have hpk : k < p := by nlinarith
  have hden : 0 < a * (p - k) := mul_pos ha0 (by linarith)
  set c := (a * p - k) / (a * (p - k)) with hc
  have hc0 : 0 < c := div_pos (by linarith) hden
  have hc1 : c < 1 := by rw [div_lt_one hden]; nlinarith
  have ht := intervalIntegral_tendsto_integral_Ioi (μ := volume) 0 hφ.integrable tendsto_id
  rw [hφ.total] at ht
  obtain ⟨b, hb⟩ := (ht.eventually (lt_mem_nhds hc1)).exists_forall_of_atTop
  set b' := max b 1
  have hb' : c < ∫ s in (0:ℝ)..b', φ s := hb b' (le_max_left _ _)
  have hb'0 : 0 ≤ b' := le_trans zero_le_one (le_max_right _ _)
  have hcont : ContinuousOn (fun x => ∫ s in (0:ℝ)..x, φ s) (Set.Icc 0 b') := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := b') (f := φ)
      (by rw [Set.uIcc_of_le hb'0, integrableOn_Icc_iff_integrableOn_Ioc]
          exact hφ.integrable.mono_set Set.Ioc_subset_Ioi_self)
    rwa [Set.uIcc_of_le hb'0] at this
  have hivt := intermediate_value_Icc hb'0 hcont
  obtain ⟨x, hx, hxc⟩ := hivt ⟨by simp; linarith, hb'.le⟩
  refine ⟨x, hx.1, (root_iff k p a φ hk hp hφ ha0 ha1 hapk hx.1).2 hxc, fun y hy hroot => ?_⟩
  have hyc := (root_iff k p a φ hk hp hφ ha0 ha1 hapk hy).1 hroot
  rcases lt_trichotomy y x with h | h | h
  · have := dd_strict hφ hy h; simp only at hxc; linarith
  · exact h
  · have := dd_strict hφ hx.1 h; simp only at hxc; linarith

end BellmanDP.Inventory

open BellmanDP.Inventory


theorem solution (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p) :
    (∀ y : ℝ, 0 ≤ y →
      (StockLevelRoot k p a φ y ↔ (∫ s in (0 : ℝ)..y, φ s) = (a * p - k) / (a * (p - k)))) ∧
    ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
      ∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar := by
  exact root_core k p a φ hk hp hφ ha0 ha1 hapk
