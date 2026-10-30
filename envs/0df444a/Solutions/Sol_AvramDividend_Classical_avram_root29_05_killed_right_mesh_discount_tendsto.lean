-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_killed_right_mesh_discount_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:26:38.032992+00:00
-- url     : https://prove2.me/submissions/6188e51a-34f0-46ca-9a91-234842e070f0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_right_mesh_endpoint_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal Classical

/-- The discounted weight of the first mesh endpoint at or after a payment
time converges to its strict-killing discount, including the ruin boundary. -/
theorem solution (r q : ℝ) (τ : ℝ≥0∞) :
    Tendsto (fun n : ℕ =>
      let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
      if ENNReal.ofReal e < τ then
        ENNReal.ofReal (Real.exp (-(q * e))) else 0)
      atTop (𝓝 (if ENNReal.ofReal r < τ then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0)) := by
  let e : ℕ → ℝ := fun n =>
    ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 r) := by
    simpa [e] using
      (AvramDividend.Classical.avram_root29_05_right_mesh_endpoint_tendsto r)
  have hcoe : Tendsto (fun n => ENNReal.ofReal (e n))
      atTop (𝓝 (ENNReal.ofReal r)) :=
    (ENNReal.continuous_ofReal.tendsto r).comp he
  have hw : Tendsto (fun n => ENNReal.ofReal (Real.exp (-(q * e n))))
      atTop (𝓝 (ENNReal.ofReal (Real.exp (-(q * r))))) := by
    have hc : Continuous (fun t : ℝ =>
        ENNReal.ofReal (Real.exp (-(q * t)))) :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))
    exact (hc.tendsto r).comp he
  change Tendsto (fun n =>
    if ENNReal.ofReal (e n) < τ then
      ENNReal.ofReal (Real.exp (-(q * e n))) else 0)
    atTop (𝓝 (if ENNReal.ofReal r < τ then
      ENNReal.ofReal (Real.exp (-(q * r))) else 0))
  by_cases h : ENNReal.ofReal r < τ
  · have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (e n) < τ :=
      hcoe.eventually (isOpen_Iio.mem_nhds h)
    simp only [if_pos h]
    apply hw.congr'
    filter_upwards [hev] with n hn
    simp [hn]
  · have hlow (n : ℕ) : r ≤ e n := by
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hc : r * ((n : ℝ) + 1) ≤
          ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) := Int.le_ceil _
      dsimp [e]
      exact (le_div_iff₀ hp).2 hc
    have hn (n : ℕ) : ¬ ENNReal.ofReal (e n) < τ := by
      exact not_lt.mpr
        ((not_lt.mp h).trans (ENNReal.ofReal_le_ofReal (hlow n)))
    simpa [h, hn] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞))
        atTop (𝓝 0))
