-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB113_floor_stopped_clipped_coefficient_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:44:00.958445+00:00
-- url     : https://prove2.me/submissions/2256826a-d307-4337-b829-192a3c140114

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB105_original_uniform_floor_left_endpoint_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB106_clipped_derivative_tendsto_off_endpoints
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set AvramDividend.Classical
noncomputable section

theorem solution
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (q : ℝ) (w : ℝ → ℝ) (a b : ℝ)
    (Y : ℝ → ℝ) (hY : ContinuousAt Y t)
    (hCont : Y t ∈ Ioo a b → ContinuousAt (deriv w) (Y t))
    (ha : Y t ≠ a) (hb : Y t ≠ b)
    (ρ : ℝ) (hρ : t ≠ ρ) :
    let s : ℕ → ℝ := fun m =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      ((⌊t / Δ⌋₊ : ℕ) : ℝ) * Δ
    Tendsto (fun m : ℕ =>
      if s m < ρ then
        Real.exp (-(q * s m)) *
          (if Y (s m) ∈ Icc a b then deriv w (Y (s m)) else 1)
      else 0) atTop
      (𝓝 (if t < ρ then
        Real.exp (-(q * t)) *
          (if Y t ∈ Icc a b then deriv w (Y t) else 1)
      else 0)) := by
  intro s
  have hTime : Tendsto s atTop (𝓝 t) :=
    avram_gbB105_original_uniform_floor_left_endpoint_tendsto
      n hn t (le_of_lt ht)
  have hYt : Tendsto (fun m => Y (s m)) atTop (𝓝 (Y t)) :=
    hY.tendsto.comp hTime
  have hClip :=
    avram_gbB106_clipped_derivative_tendsto_off_endpoints
      w a b (Y t) hCont ha hb (fun m => Y (s m)) hYt
  have hExpCont : ContinuousAt
      (fun z : ℝ => Real.exp (-(q * z))) t := by fun_prop
  have hExp : Tendsto (fun m => Real.exp (-(q * s m)))
      atTop (𝓝 (Real.exp (-(q * t)))) :=
    hExpCont.tendsto.comp hTime
  have hProd := hExp.mul hClip
  by_cases hlt : t < ρ
  · have hEv : ∀ᶠ m in atTop, s m < ρ :=
      hTime.eventually (isOpen_Iio.mem_nhds hlt)
    have heq : (fun m : ℕ =>
        if s m < ρ then Real.exp (-(q * s m)) *
          (if Y (s m) ∈ Icc a b then deriv w (Y (s m)) else 1)
        else 0) =ᶠ[atTop] (fun m =>
          Real.exp (-(q * s m)) *
            (if Y (s m) ∈ Icc a b then deriv w (Y (s m)) else 1)) := by
      filter_upwards [hEv] with m hm
      exact if_pos hm
    simpa [hlt] using (hProd.congr' heq.symm)
  · have hGt : ρ < t :=
      lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hρ)
    have hEv : ∀ᶠ m in atTop, ρ < s m :=
      hTime.eventually (isOpen_Ioi.mem_nhds hGt)
    have heq : (fun m : ℕ =>
        if s m < ρ then Real.exp (-(q * s m)) *
          (if Y (s m) ∈ Icc a b then deriv w (Y (s m)) else 1)
        else 0) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [hEv] with m hm
      exact if_neg (not_lt_of_ge (le_of_lt hm))
    simpa [hlt] using (tendsto_const_nhds.congr' heq.symm)
