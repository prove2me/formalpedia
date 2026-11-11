-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18h_uniform_cutoff_rate_rightcont_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:41:43.125495+00:00
-- url     : https://prove2.me/submissions/4a87b40d-3613-4d47-95c9-20aa2cb31872

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original sequence admits a right-continuous same-time-index limit
from one deterministic locally uniform Cauchy rate. -/
theorem solution
    (f : ℕ → ℝ≥0 → ℝ)
    (hRight : ∀ (n : ℕ) (t : ℝ≥0),
      ContinuousWithinAt (f n) (Ici t) t)
    (hZero : ∀ n : ℕ, f n 0 = 0)
    (hRate : ∀ T : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0), t ≤ T →
        |f m t - f n t| ≤ (1 / ((n : ℝ) + 1)) * C) :
    ∃ g : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        Tendsto (fun n : ℕ => f n t) atTop (𝓝 (g t))) ∧
      (∀ t : ℝ≥0, ContinuousWithinAt g (Ici t) t) ∧
      g 0 = 0 := by
  classical
  have hUCauchy (T : ℝ≥0) : UniformCauchySeqOn f atTop (Iic T) := by
    obtain ⟨C, hC, hBound⟩ := hRate T
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    have hTend : Tendsto
        (fun n : ℕ => (1 / ((n : ℝ) + 1)) * C) atTop (𝓝 (0 : ℝ)) := by
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          (1 / ((n : ℝ) + 1)) * C < ε / 2 :=
      hTend.eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨N, hN⟩ := hEventually.exists
    refine ⟨N, ?_⟩
    intro m hm n hn x hx
    have hm' := hBound N m hm x hx
    have hn' := hBound N n hn x hx
    rw [Real.dist_eq]
    have htriangle :
        |f m x - f n x| ≤
          |f m x - f N x| + |f n x - f N x| := by
      calc
        |f m x - f n x| =
            |(f m x - f N x) + (f N x - f n x)| := by ring
        _ ≤ |f m x - f N x| + |f N x - f n x| :=
          abs_add_le _ _
        _ = |f m x - f N x| + |f n x - f N x| := by
          rw [abs_sub_comm (f N x) (f n x)]
    linarith
  have hPoint (t : ℝ≥0) :
      ∃ y : ℝ, Tendsto (fun n : ℕ => f n t) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete
      ((hUCauchy t).cauchySeq (mem_Iic.mpr le_rfl))
  let g (t : ℝ≥0) : ℝ := Classical.choose (hPoint t)
  have hg (t : ℝ≥0) :
      Tendsto (fun n : ℕ => f n t) atTop (𝓝 (g t)) :=
    Classical.choose_spec (hPoint t)
  have hUniform (T : ℝ≥0) :
      TendstoUniformlyOn f g atTop (Iic T) :=
    (hUCauchy T).tendstoUniformlyOn_of_tendsto
      (fun t _ => hg t)
  refine ⟨g, hg, ?_, ?_⟩
  · intro t
    have htT : t < t + 1 := by simp
    have hLocal : Iic (t + 1) ∈ 𝓝[Ici t] t := by
      apply Filter.mem_of_superset
        (nhdsWithin_le_nhds (Iio_mem_nhds htT))
      intro y hy
      exact le_of_lt (mem_Iio.mp hy)
    apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt
      (show t ∈ Ici t by simp)
    intro u hu
    obtain ⟨n, hn⟩ := (hUniform (t + 1) u hu).exists
    exact ⟨Iic (t + 1), hLocal, f n, hRight n t, hn⟩
  · have hZeroTend :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (g 0)) := by
      simpa only [hZero] using hg 0
    exact tendsto_nhds_unique hZeroTend tendsto_const_nhds
