-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a112_original_gaussian_random_crossing_compensator_small_from_source_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:56:20.182206+00:00
-- url     : https://prove2.me/submissions/f8fa7c27-506c-4b59-b36b-d2417bf7045c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
noncomputable section

/-- Uniform compact derivative bounds turn small original Gaussian full-source crossing increment and vanishing physical mesh into a vanishing compensated HJB crossing term. -/
theorem solution
    (Z Δ H : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hΔ : ∀ m, 0 ≤ Δ m)
    (hError : ∀ m,
      |H m| ≤ K * (|Z m| + (Z m)^2 + Δ m))
    (hZ : Tendsto Z atTop (𝓝 (0 : ℝ)))
    (hΔlim : Tendsto Δ atTop (𝓝 (0 : ℝ))) :
    Tendsto H atTop (𝓝 (0 : ℝ)) := by
  have hSum : Tendsto (fun m => |Z m| + (Z m)^2 + Δ m)
      atTop (𝓝 (0 : ℝ)) := by
    convert ((hZ.abs.add (hZ.pow 2)).add hΔlim) using 1 <;> norm_num
  have hUpper : Tendsto
      (fun m => K * (|Z m| + (Z m)^2 + Δ m))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hSum.const_mul K
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.1 hUpper) ε hε
  refine ⟨N, ?_⟩
  intro m hm
  have hzAbs : 0 ≤ |Z m| := abs_nonneg _
  have hzSq : 0 ≤ (Z m)^2 := sq_nonneg _
  have hNonneg : 0 ≤ K * (|Z m| + (Z m)^2 + Δ m) :=
    mul_nonneg hK (by linarith [hΔ m])
  have hSmall : K * (|Z m| + (Z m)^2 + Δ m) < ε := by
    have h := hN m hm
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg] using h
  change dist (H m) (0 : ℝ) < ε
  simpa only [Real.dist_eq, sub_zero] using
    (lt_of_le_of_lt (hError m) hSmall)
