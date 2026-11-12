-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:21:32.474303+00:00
-- url     : https://prove2.me/submissions/3a7d44a9-3657-436f-878c-6dfd9d932b5b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- L2 convergence yields absolute L1 convergence on every restricted event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 P) (hg : MemLp g 2 P)
    (hL2 : Tendsto (fun n : ℕ => eLpNorm (f n - g) 2 P)
      atTop (𝓝 (0 : ℝ≥0∞))) :
    Tendsto (fun n : ℕ => ∫ ω in A, |g ω - f n ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  have hDiff (n : ℕ) : MemLp (f n - g) 2 P := (hf n).sub hg
  have hLp2 : Tendsto (fun n : ℕ => lpNorm (f n - g) 2 P)
      atTop (𝓝 (0 : ℝ)) := by
    have hReal := ((ENNReal.continuousAt_toReal
      (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hL2)
    have heq (n : ℕ) :
        lpNorm (f n - g) 2 P = (eLpNorm (f n - g) 2 P).toReal :=
      (toReal_eLpNorm (hDiff n).aestronglyMeasurable).symm
    change Tendsto (fun n : ℕ =>
      (eLpNorm (f n - g) 2 P).toReal) atTop (𝓝 (0 : ℝ)) at hReal
    simpa only [heq] using hReal
  have hLpBound (n : ℕ) :
      lpNorm (f n - g) 1 P ≤ lpNorm (f n - g) 2 P := by
    have hENN := eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hDiff n).aestronglyMeasurable
    have hReal := ENNReal.toReal_mono (hDiff n).eLpNorm_ne_top hENN
    simpa only [toReal_eLpNorm (hDiff n).aestronglyMeasurable] using hReal
  have hLp1 : Tendsto (fun n : ℕ => lpNorm (f n - g) 1 P)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Tendsto.squeeze
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      hLp2
    · intro n
      exact lpNorm_nonneg
    · exact hLpBound
  have hGlobal : Tendsto
      (fun n : ℕ => ∫ ω, |g ω - f n ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    have heq (n : ℕ) :
        (∫ ω, |g ω - f n ω| ∂P) = lpNorm (f n - g) 1 P := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using
        (lpNorm_one_eq_integral_norm
          (hDiff n).aestronglyMeasurable).symm
    simpa only [heq] using hLp1
  apply Filter.Tendsto.squeeze
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hGlobal
  · intro n
    exact integral_nonneg (fun ω => abs_nonneg _)
  · intro n
    have hI : Integrable (fun ω => |g ω - f n ω|) P := by
      simpa only [Pi.sub_apply, abs_sub_comm] using
        ((hDiff n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).abs
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun ω => abs_nonneg _)) hI
