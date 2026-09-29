-- Prove2me | solution 1 for ErlerGross.midpoint_uncertainty_diverges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T04:35:05.277848+00:00
-- url     : https://prove2.me/submissions/9f74725b-6a70-4d05-b677-b6a2ee3e72cd

import Mathlib
import Definitions.Def_ErlerGross_defs

set_option autoImplicit false

open Real Filter Topology MeasureTheory ErlerGross in
theorem solution (ω : ℕ → ℝ)
    (hω : Tendsto (fun n : ℕ => ω (2 * n)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((-1 : ℝ) ^ (n + 1) - ω (2 * (n + 1))) ^ 2 / (2 * ((n : ℝ) + 1)))
      atTop atTop := by
  have hnn : ∀ n : ℕ, 0 ≤ ((-1 : ℝ) ^ (n + 1) - ω (2 * (n + 1))) ^ 2 / (2 * ((n : ℝ) + 1)) :=
    fun n => div_nonneg (sq_nonneg _) (by positivity)
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg hnn]
  intro hs
  have hω' : Tendsto (fun n : ℕ => ω (2 * (n + 1))) atTop (𝓝 0) :=
    hω.comp (tendsto_add_atTop_nat 1)
  have habs := hω'.abs
  rw [abs_zero] at habs
  have hev : ∀ᶠ n in atTop, |ω (2 * (n + 1))| < 1 / 2 :=
    habs.eventually (gt_mem_nhds (by norm_num))
  have hsum : Summable (fun n : ℕ => (1 / 8 : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹) := by
    refine Summable.of_norm_bounded_eventually hs ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hkey : 1 / 4 ≤ ((-1 : ℝ) ^ (n + 1) - ω (2 * (n + 1))) ^ 2 := by
      have h2 := abs_lt.mp hn
      rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> nlinarith
    have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hpos]
    push_cast
    have hq : 1 / 8 * ((n : ℝ) + 1)⁻¹ * (2 * ((n : ℝ) + 1)) = 1 / 4 := by
      field_simp
      ring
    linarith
  have h2 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) :=
    (hsum.mul_left 8).congr (fun n => by ring)
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp h2)
