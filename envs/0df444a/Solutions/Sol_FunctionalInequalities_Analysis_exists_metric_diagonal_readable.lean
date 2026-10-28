-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_metric_diagonal_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:57.357251+00:00
-- url     : https://prove2.me/submissions/003b39df-1781-4d90-9a16-d313ab84d04b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_DiagonalSelector

open Filter Topology
/-- **Metric diagonal selection**: if each row `G n ·` converges to `F n` and `F → x` in a pseudometric
space, there are indices `k n ≥ n`, `k → ∞`, with `G n (k n) → x`. -/
theorem solution {X : Type*} [PseudoMetricSpace X]
    (G : ℕ → ℕ → X) (F : ℕ → X) (x : X)
    (hrow : ∀ n : ℕ, Tendsto (G n) atTop (𝓝 (F n))) (houter : Tendsto F atTop (𝓝 x)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ Tendsto k atTop atTop ∧
      Tendsto (fun n => G n (k n)) atTop (𝓝 x) := by
  have hchoose (n : ℕ) : ∃ k : ℕ, n ≤ k ∧ dist (G n k) (F n) < 1 / ((n : ℝ) + 1) := by
    have hsmall : ∀ᶠ k in atTop, G n k ∈ Metric.ball (F n) (1 / ((n : ℝ) + 1)) :=
      (hrow n).eventually (Metric.ball_mem_nhds (F n) (by positivity))
    obtain ⟨k, hkl, hks⟩ := ((eventually_ge_atTop n).and hsmall).exists
    exact ⟨k, hkl, by simpa only [Metric.mem_ball] using hks⟩
  choose k hkl hks using hchoose
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hkl n)
  have hdist : Tendsto (fun n => dist (G n (k n)) (F n)) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => dist_nonneg) (fun n => (hks n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have houterDist : Tendsto (fun n => dist (F n) x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [dist_self] using houter.dist (tendsto_const_nhds (x := x))
  have hlimDist : Tendsto (fun n => dist (G n (k n)) x) atTop (𝓝 (0 : ℝ)) := by
    have hsum := hdist.add houterDist
    simp only [add_zero] at hsum
    exact squeeze_zero (fun n => dist_nonneg) (fun n => dist_triangle _ _ _) hsum
  exact ⟨k, hkl, hk, (tendsto_iff_dist_tendsto_zero).2 hlimDist⟩
