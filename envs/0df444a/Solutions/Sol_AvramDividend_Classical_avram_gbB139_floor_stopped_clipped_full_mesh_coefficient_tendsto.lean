-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB139_floor_stopped_clipped_full_mesh_coefficient_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:02:32.624204+00:00
-- url     : https://prove2.me/submissions/faf10d28-8433-431a-b4c1-f94df0df4a86

import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Theorems.Thm_AvramDividend_Classical_avram_gbB113_floor_stopped_clipped_coefficient_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set AvramDividend.Classical
noncomputable section

theorem solution
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (n : ℝ))
    (q : ℝ) (w : ℝ → ℝ) (a b : ℝ)
    (Y : ℝ → ℝ) (hY : ContinuousAt Y t)
    (hCont : Y t ∈ Ioo a b → ContinuousAt (deriv w) (Y t))
    (ha : Y t ≠ a) (hb : Y t ≠ b)
    (ρ : ℝ) (hρ : t ≠ ρ) :
    let K : ℕ → ℝ := fun m =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ := (i : ℝ) * Δ
        if s ≤ t ∧ t < (((i + 1 : ℕ) : ℝ) * Δ) then
          if s < ρ then Real.exp (-(q * s)) *
            (if Y s ∈ Icc a b then deriv w (Y s) else 1)
          else 0 else 0)
    Tendsto K atTop (𝓝 (if t < ρ then
      Real.exp (-(q * t)) *
        (if Y t ∈ Icc a b then deriv w (Y t) else 1)
      else 0)) := by
  intro K
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB (m : ℕ) : K m =
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      let s : ℝ := ((⌊t / Δ⌋₊ : ℕ) : ℝ) * Δ
      if s < ρ then Real.exp (-(q * s)) *
        (if Y s ∈ Icc a b then deriv w (Y s) else 1)
      else 0 := by
    let c : ℕ → ℝ := fun i =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      let s : ℝ := (i : ℝ) * Δ
      if s < ρ then Real.exp (-(q * s)) *
        (if Y s ∈ Icc a b then deriv w (Y s) else 1)
      else 0
    have heq := avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
      (n : ℝ) hnR m c t ⟨le_of_lt ht.1, ht.2⟩
    simpa only [K, c] using heq
  have hLim := avram_gbB113_floor_stopped_clipped_coefficient_tendsto
    n hn t ht.1 q w a b Y hY hCont ha hb ρ hρ
  change Tendsto (fun m : ℕ => K m) atTop _
  simpa only [hB] using hLim
