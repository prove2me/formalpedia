-- Prove2me | solution 1 for FunctionalInequalities.Energy.locallyLipschitz_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:36.486884+00:00
-- url     : https://prove2.me/submissions/b27a41a2-2bdb-4e16-abbb-6be67efe7589

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
section Reduction
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [InnerProductSpace ℝ V] in
/-- the local Lipschitz product rule.  A locally Lipschitz function times a bounded globally Lipschitz one is locally
Lipschitz. -/
theorem solution {g h : V → ℝ} {N : ℝ≥0} (hg : LocallyLipschitz g)
    (hh : LipschitzWith N h) (hh1 : ∀ x, |h x| ≤ 1) :
    LocallyLipschitz (fun x ↦ g x * h x) := by
  intro x
  obtain ⟨K, t, ht, hK⟩ := hg x
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  set s : Set V := Metric.ball x (min r 1) with hs
  have hsub : s ⊆ t := (Metric.ball_subset_ball (min_le_left _ _)).trans hrt
  have hxs : x ∈ s := Metric.mem_ball_self (lt_min hr one_pos)
  have hKs : LipschitzOnWith K g s := hK.mono hsub
  have hbound : ∀ y ∈ s, |g y| ≤ |g x| + K := by
    intro y hy
    have : dist (g y) (g x) ≤ K * dist y x := hKs.dist_le_mul y hy x hxs
    have hd : dist y x < 1 := lt_of_lt_of_le (by simpa [hs, Metric.mem_ball] using hy)
      (min_le_right _ _)
    have : |g y - g x| ≤ K * dist y x := by simpa [Real.dist_eq] using this
    have h2 : |g y| ≤ |g x| + K * dist y x := by
      have := abs_sub_abs_le_abs_sub (g y) (g x)
      linarith [abs_nonneg (g x)]
    refine h2.trans ?_
    have : K * dist y x ≤ K * 1 := by
      exact mul_le_mul_of_nonneg_left hd.le K.coe_nonneg
    linarith
  refine ⟨(K + (|g x| + K) * N).toNNReal, s, Metric.isOpen_ball.mem_nhds hxs, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
  have hCnn : (0 : ℝ) ≤ K + (|g x| + K) * N := by positivity
  rw [Real.coe_toNNReal _ hCnn]
  have hgyz : |g y - g z| ≤ K * dist y z := by
    simpa [Real.dist_eq] using hKs.dist_le_mul y hy z hz
  have hhyz : |h y - h z| ≤ N * dist y z := by
    simpa [Real.dist_eq] using hh.dist_le_mul y z
  have hkey : g y * h y - g z * h z = (g y - g z) * h y + g z * (h y - h z) := by ring
  have h1 : |(g y - g z) * h y| ≤ K * dist y z := by
    rw [abs_mul]
    calc |g y - g z| * |h y| ≤ (K * dist y z) * 1 := by
          apply mul_le_mul hgyz (hh1 y) (abs_nonneg _)
          positivity
      _ = K * dist y z := by ring
  have h2 : |g z * (h y - h z)| ≤ (|g x| + K) * (N * dist y z) := by
    rw [abs_mul]
    exact mul_le_mul (hbound z hz) hhyz (abs_nonneg _) (by positivity)
  calc dist (g y * h y) (g z * h z) = |(g y - g z) * h y + g z * (h y - h z)| := by
        rw [Real.dist_eq, hkey]
    _ ≤ |(g y - g z) * h y| + |g z * (h y - h z)| := abs_add_le _ _
    _ ≤ K * dist y z + (|g x| + K) * (N * dist y z) := add_le_add h1 h2
    _ = (K + (|g x| + K) * N) * dist y z := by ring
