-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB106_clipped_derivative_tendsto_off_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:41:08.763282+00:00
-- url     : https://prove2.me/submissions/27bad5c6-ebc1-45d2-840e-8827f5b7fd60

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set
noncomputable section

theorem solution
    (w : ℝ → ℝ) (a b y : ℝ)
    (hCont : y ∈ Ioo a b → ContinuousAt (deriv w) y)
    (ha : y ≠ a) (hb : y ≠ b)
    (Y : ℕ → ℝ) (hY : Tendsto Y atTop (𝓝 y)) :
    Tendsto (fun m : ℕ => if Y m ∈ Icc a b then
      deriv w (Y m) else 1) atTop
      (𝓝 (if y ∈ Icc a b then deriv w y else 1)) := by
  by_cases hin : y ∈ Icc a b
  · have hlo : a < y := lt_of_le_of_ne hin.1 (Ne.symm ha)
    have hhi : y < b := lt_of_le_of_ne hin.2 hb
    have hT : Tendsto (fun m => deriv w (Y m)) atTop
        (𝓝 (deriv w y)) :=
      (hCont ⟨hlo, hhi⟩).tendsto.comp hY
    have he : ∀ᶠ m in atTop, Y m ∈ Icc a b := by
      filter_upwards [hY.eventually (isOpen_Ioo.mem_nhds ⟨hlo, hhi⟩)]
        with m hm
      exact ⟨le_of_lt hm.1, le_of_lt hm.2⟩
    have heq : (fun m => if Y m ∈ Icc a b then deriv w (Y m) else 1)
        =ᶠ[atTop] (fun m => deriv w (Y m)) := by
      filter_upwards [he] with m hm
      exact if_pos hm
    simpa [hin] using (hT.congr' heq.symm)
  · have hout : y < a ∨ b < y := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hin
    rcases hout with hlt | hgt
    · have he : ∀ᶠ m in atTop, Y m < a :=
        hY.eventually (isOpen_Iio.mem_nhds hlt)
      have heq : (fun m => if Y m ∈ Icc a b then deriv w (Y m) else 1)
          =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
        filter_upwards [he] with m hm
        exact if_neg (fun h => (not_le_of_gt hm) h.1)
      simpa [hin] using (tendsto_const_nhds.congr' heq.symm)
    · have he : ∀ᶠ m in atTop, b < Y m :=
        hY.eventually (isOpen_Ioi.mem_nhds hgt)
      have heq : (fun m => if Y m ∈ Icc a b then deriv w (Y m) else 1)
          =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
        filter_upwards [he] with m hm
        exact if_neg (fun h => (not_le_of_gt hm) h.2)
      simpa [hin] using (tendsto_const_nhds.congr' heq.symm)
