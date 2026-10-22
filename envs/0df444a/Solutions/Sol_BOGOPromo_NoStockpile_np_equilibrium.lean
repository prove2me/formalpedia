-- Prove2me | solution 1 for BOGOPromo.NoStockpile.np_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:48:25.666153+00:00
-- url     : https://prove2.me/submissions/099d5190-b75f-410f-a81d-ff49be8fec49

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

set_option autoImplicit false

open MeasureTheory BOGOPromo.NoStockpile

theorem ite_int_aux (a p : ℝ) (hp : 0 ≤ p) :
    ∫ v in (0:ℝ)..1, (if p ≤ v then a else 0) = a * max (1 - p) 0 := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have : (fun v : ℝ => if p ≤ v then a else 0) = (Set.Ici p).indicator (fun _ => a) := by
    ext v; simp [Set.indicator]
  rw [this, setIntegral_indicator measurableSet_Ici, setIntegral_const]
  have hv : volume (Set.Ioc (0:ℝ) 1 ∩ Set.Ici p) = ENNReal.ofReal (max (1 - p) 0) := by
    rcases le_or_gt p 1 with h | h
    · rw [max_eq_left (by linarith)]
      apply le_antisymm
      · calc volume (Set.Ioc (0:ℝ) 1 ∩ Set.Ici p) ≤ volume (Set.Icc p 1) := by
              apply measure_mono
              intro v hv; exact ⟨hv.2, hv.1.2⟩
          _ = ENNReal.ofReal (1 - p) := Real.volume_Icc
      · calc ENNReal.ofReal (1 - p) = volume (Set.Ioc p 1) := Real.volume_Ioc.symm
          _ ≤ _ := by
              apply measure_mono
              intro v hv; exact ⟨⟨by linarith [hv.1], hv.2⟩, le_of_lt hv.1⟩
    · rw [max_eq_right (by linarith)]
      have : Set.Ioc (0:ℝ) 1 ∩ Set.Ici p = ∅ := by
        ext v; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 h2; linarith [h1.2]
      rw [this]; simp
  rw [Measure.real, hv, ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul, mul_comm]

theorem npProfit_eq (w p : ℝ) (hp : 0 ≤ p) : npProfit w p = 2 * (p - w) * max (1 - p) 0 := by
  unfold npProfit; exact ite_int_aux _ _ hp

theorem npDemand_eq (p : ℝ) (hp : 0 ≤ p) : npDemand p = 2 * max (1 - p) 0 := by
  unfold npDemand; rw [ite_int_aux _ _ hp]

theorem br_unique (w p : ℝ) (hw : w ∈ Set.Ioc (0:ℝ) 1) (hbr : IsBestRespN w p) :
    npDemand p = 1 - w ∧ (w < 1 → p = (1 + w) / 2) := by
  obtain ⟨hp0, hbest⟩ := hbr
  have hw0 := hw.1; have hw1 := hw.2
  have hq : (0:ℝ) ≤ (1 + w) / 2 := by linarith
  have hb := hbest ((1 + w) / 2) hq
  rw [npProfit_eq w _ hq, npProfit_eq w p hp0] at hb
  rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - (1 + w) / 2)] at hb
  have hp1 : p ≤ 1 ∨ 1 < p := le_or_gt p 1
  rcases hp1 with h1 | h1
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - p)] at hb
    have hsq : (1 + w - 2 * p) ^ 2 ≤ 0 := by nlinarith [hb]
    have hz : 1 + w - 2 * p = 0 := by
      have : (1 + w - 2 * p) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have hpe : p = (1 + w) / 2 := by linarith
    refine ⟨?_, fun _ => hpe⟩
    rw [npDemand_eq p hp0, max_eq_left (by linarith)]; rw [hpe]; ring
  · rw [max_eq_right (by linarith : 1 - p ≤ 0)] at hb
    have : w = 1 := by nlinarith [hb]
    subst this
    refine ⟨?_, fun h => by linarith⟩
    rw [npDemand_eq p hp0, max_eq_right (by linarith)]; ring

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∃ (w : ℝ) (r : ℝ → ℝ), IsEqN c w r) ∧
    ∀ (w : ℝ) (r : ℝ → ℝ), IsEqN c w r →
      w = (1 + c) / 2 ∧ r w = (3 + c) / 4 ∧ npDemand (r w) = (1 - c) / 2 ∧
      npProfit w (r w) = (1 - c) ^ 2 / 8 ∧ (w - c) * npDemand (r w) = (1 - c) ^ 2 / 4 := by
  constructor
  · refine ⟨(1 + c) / 2, fun w' => (1 + w') / 2, ?_, ?_, ?_⟩
    · constructor <;> linarith
    · intro w' hw'
      have hq : (0:ℝ) ≤ (1 + w') / 2 := by linarith [hw'.1]
      refine ⟨hq, fun p' hp' => ?_⟩
      rw [npProfit_eq _ _ hp', npProfit_eq _ _ hq, max_eq_left (by linarith [hw'.2] : (0:ℝ) ≤ 1 - (1 + w') / 2)]
      rcases le_or_gt p' 1 with h | h
      · rw [max_eq_left (by linarith)]
        nlinarith [sq_nonneg (1 + w' - 2 * p')]
      · rw [max_eq_right (by linarith)]
        nlinarith [sq_nonneg (1 - w'), hw'.2]
    · intro w' hw'
      have hq : (0:ℝ) ≤ (1 + w') / 2 := by linarith [hw'.1]
      rw [npDemand_eq _ hq, npDemand_eq _ (by linarith [hw'.1] : (0:ℝ) ≤ (1 + (1 + c) / 2) / 2)]
      rw [max_eq_left (by linarith [hw'.2] : (0:ℝ) ≤ 1 - (1 + w') / 2),
        max_eq_left (by linarith : (0:ℝ) ≤ 1 - (1 + (1 + c) / 2) / 2)]
      nlinarith [sq_nonneg (w' - (1 + c) / 2)]
  · intro w r ⟨hw, hbr, hopt⟩
    have hd : ∀ w' ∈ Set.Ioc (0:ℝ) 1, npDemand (r w') = 1 - w' := fun w' hw' =>
      (br_unique w' (r w') hw' (hbr w' hw')).1
    have hwc : (1 + c) / 2 ∈ Set.Ioc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have h := hopt ((1 + c) / 2) hwc
    rw [hd _ hwc, hd w hw] at h
    have hsq : (w - (1 + c) / 2) ^ 2 ≤ 0 := by nlinarith [h]
    have hwe : w = (1 + c) / 2 := by
      have : (w - (1 + c) / 2) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
      have := pow_eq_zero_iff (two_ne_zero) |>.mp this
      linarith
    have hw1 : w < 1 := by rw [hwe]; linarith
    have hr : r w = (3 + c) / 4 := by
      rw [(br_unique w (r w) hw (hbr w hw)).2 hw1, hwe]; ring
    have hrnn : 0 ≤ r w := (hbr w hw).1
    refine ⟨hwe, hr, ?_, ?_, ?_⟩
    · rw [hd w hw, hwe]; ring
    · rw [npProfit_eq _ _ hrnn, hr, hwe, max_eq_left (by linarith)]; ring
    · rw [hd w hw, hwe]; ring
