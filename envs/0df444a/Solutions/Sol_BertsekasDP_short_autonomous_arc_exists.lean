-- Prove2me | solution 1 for BertsekasDP.short_autonomous_arc_exists
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T23:02:41.942507+00:00
-- url     : https://prove2.me/submissions/779056df-3f19-4edb-8118-e9c90549a18c

import Definitions.Def_BertsekasCTModel

open Filter Metric Set ODE
open scoped Topology NNReal

private lemma picard_curve_with_speed_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {b c : ℝ} {t₀ : Icc b c} {q x : E}
    {R r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ q R r L K)
    (hx : x ∈ closedBall q r) :
    ∃ z : ℝ → E, Continuous z ∧ z t₀ = x ∧
      (∀ t ∈ Ioo b c, HasDerivAt z (f t (z t)) t) ∧
      (∀ s ∈ Icc b c, ∀ t ∈ Icc b c, ‖z s - z t‖ ≤ L * |s - t|) := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, α.continuous_compProj, ?_, ?_, ?_⟩
  · rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · intro t ht
    have hd : HasDerivWithinAt α.compProj (f t (α.compProj t)) (Icc b c) t := by
      apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
        α.continuous_compProj.continuousOn
        (fun _ _ ↦ α.compProj_mem_closedBall hf.mul_max_le) x
        (Ioo_subset_Icc_self ht) |>.congr_of_mem _ (Ioo_subset_Icc_self ht)
      intro t' ht'
      nth_rw 1 [← hα]
      rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
    exact hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · intro s hs t ht
    rw [FunSpace.compProj_of_mem hs, FunSpace.compProj_of_mem ht, ← dist_eq_norm]
    exact α.lipschitzWith.dist_le_mul ⟨s, hs⟩ ⟨t, ht⟩

theorem solution
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ 1 f)
    (q : EuclideanSpace ℝ (Fin n)) (a : ℝ → EuclideanSpace ℝ (Fin n))
    (τ C : ℝ)
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖a ε - q‖ ≤ C * ε) :
    ∃ (y : ℝ → ℝ → EuclideanSpace ℝ (Fin n)) (K : ℝ),
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ContinuousOn (y ε) (Set.Icc (τ - ε) τ) ∧
        y ε (τ - ε) = a ε ∧
        (∀ t ∈ Set.Ioo (τ - ε) τ, HasDerivAt (y ε) (f (y ε t)) t) ∧
        (∀ t ∈ Set.Icc (τ - ε) τ, ‖y ε t - q‖ ≤ K * ε) := by
  classical
  obtain ⟨d, hd, R, r, L, B, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one (hf.contDiffAt (x := q))
  have hcurves (ε : ℝ) : ∃ z : ℝ → EuclideanSpace ℝ (Fin n),
      a ε ∈ closedBall q r →
        Continuous z ∧ z (τ - ε) = a ε ∧
        (∀ t ∈ Ioo (τ - ε - d) (τ - ε + d), HasDerivAt z (f (z t)) t) ∧
        (∀ s ∈ Icc (τ - ε - d) (τ - ε + d),
          ∀ t ∈ Icc (τ - ε - d) (τ - ε + d), ‖z s - z t‖ ≤ L * |s - t|) := by
    by_cases h : a ε ∈ closedBall q r
    · obtain ⟨z, hz⟩ := picard_curve_with_speed_bound (hpl (τ - ε)) h
      exact ⟨z, fun _ ↦ hz⟩
    · exact ⟨fun _ ↦ q, fun h' ↦ (h h').elim⟩
  choose y hy using hcurves
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε < (r : ℝ) := by
    have hlim : Tendsto (fun ε : ℝ ↦ C * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [id_eq, mul_zero] using
        (tendsto_const_nhds (x := C)).mul
          ((tendsto_id : Tendsto (fun ε : ℝ ↦ ε) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
            nhdsWithin_le_nhds)
    exact hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < r from hr))
  refine ⟨y, (L : ℝ) + C, ?_⟩
  filter_upwards [ha, hsmall, self_mem_nhdsWithin,
    (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < d from
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hd))]
    with ε haε hrε hε hdε
  have hε : 0 < ε := hε
  have hdε : ε < d := hdε
  have hball : a ε ∈ closedBall q r := mem_closedBall_iff_norm.mpr (haε.trans hrε.le)
  obtain ⟨hyc, hy0, hyd, hyL⟩ := hy ε hball
  refine ⟨hyc.continuousOn, hy0, ?_, ?_⟩
  · intro t ht
    exact hyd t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    have hti : t ∈ Icc (τ - ε - d) (τ - ε + d) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h0i : τ - ε ∈ Icc (τ - ε - d) (τ - ε + d) :=
      ⟨by linarith, by linarith⟩
    calc
      ‖y ε t - q‖ ≤ ‖y ε t - y ε (τ - ε)‖ + ‖y ε (τ - ε) - q‖ :=
        norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ L * |t - (τ - ε)| + C * ε := add_le_add (hyL t hti (τ - ε) h0i)
        (by simpa only [hy0] using haε)
      _ ≤ L * ε + C * ε := by
        gcongr
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
        linarith [ht.2]
      _ = ((L : ℝ) + C) * ε := (add_mul _ _ _).symm
