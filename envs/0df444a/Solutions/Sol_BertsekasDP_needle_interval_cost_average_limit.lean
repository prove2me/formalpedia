-- Prove2me | solution 1 for BertsekasDP.needle_interval_cost_average_limit
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T22:40:05.523332+00:00
-- url     : https://prove2.me/submissions/ce4beabc-9800-4457-95ff-c169b14c3196

import Definitions.Def_BertsekasCTModel

open Set Filter MeasureTheory
open scoped Topology Interval

/-- A function continuous off a finite set is almost everywhere strongly measurable. -/
private lemma aestronglyMeasurable_of_continuousOn_diff_finset {V : Type*}
    [NormedAddCommGroup V] {a b : ℝ} (φ : ℝ → V) (Fs : Finset ℝ)
    (hcont : ContinuousOn φ (Icc a b \ (Fs : Set ℝ))) :
    AEStronglyMeasurable φ (volume.restrict (Icc a b)) := by
  have hmeas : MeasurableSet (Icc a b \ (Fs : Set ℝ)) :=
    measurableSet_Icc.diff (Fs.finite_toSet.measurableSet)
  have hae : (Icc a b \ (Fs : Set ℝ)) =ᵐ[volume] Icc a b := by
    refine diff_ae_eq_self.mpr ?_
    exact measure_mono_null inter_subset_right ((Fs.finite_toSet).measure_zero _)
  have hres : (volume : Measure ℝ).restrict (Icc a b \ (Fs : Set ℝ))
      = (volume : Measure ℝ).restrict (Icc a b) := Measure.restrict_congr_set hae
  have hm := hcont.aestronglyMeasurable (μ := (volume : Measure ℝ)) hmeas
  rwa [hres] at hm

/-- A jointly continuous integrand along a continuous state and a bounded measurable control
is interval integrable. -/
private lemma intervalIntegrable_comp_bounded {n m : ℕ} {a b : ℝ} (hab : a ≤ b)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ}
    (hG : Continuous (Function.uncurry G))
    {z : ℝ → EuclideanSpace ℝ (Fin n)} (hz : ContinuousOn z (Icc a b))
    {u : ℝ → EuclideanSpace ℝ (Fin m)}
    (hu : AEStronglyMeasurable u (volume.restrict (Icc a b)))
    {C : ℝ} (hC : ∀ s ∈ Icc a b, ‖u s‖ ≤ C) :
    IntervalIntegrable (fun s => G (z s) (u s)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hz
  have hK : IsCompact ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ×ˢ
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) C)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hfin : (volume : Measure ℝ) (Icc a b) ≠ ⊤ := by simp
  refine (integrableOn_const (C := B) hfin).mono' ?_ ?_
  · exact hG.comp_aestronglyMeasurable ((hz.aestronglyMeasurable measurableSet_Icc).prodMk hu)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    refine hB (z s, u s) ⟨?_, ?_⟩ <;>
      simp only [Metric.mem_closedBall, dist_zero_right]
    · exact hR s hs
    · exact hC s hs

/-- Averages over the shrinking window `[τ - ε, τ]` of an integrand that converges uniformly
to a constant. -/
private lemma window_average_tendsto {τ c : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hint : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable (Φ ε) volume (τ - ε) τ)
    (hclose : ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s ∈ Icc (τ - ε) τ, |Φ ε s - c| ≤ η) :
    Tendsto (fun ε => ε⁻¹ * ∫ s in (τ - ε)..τ, Φ ε s) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [hint, hclose (η / 2) (by linarith), self_mem_nhdsWithin] with ε hi hc hεp
  have hεpos : (0 : ℝ) < ε := hεp
  have hle : τ - ε ≤ τ := by linarith
  have hsub : (∫ s in (τ - ε)..τ, Φ ε s) - ε * c = ∫ s in (τ - ε)..τ, (Φ ε s - c) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hbd : |∫ s in (τ - ε)..τ, (Φ ε s - c)| ≤ (η / 2) * ε := by
    have hnorm : ‖∫ s in (τ - ε)..τ, (Φ ε s - c)‖ ≤ (η / 2) * |τ - (τ - ε)| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro s hs
      rw [uIoc_of_le hle] at hs
      rw [Real.norm_eq_abs]
      exact hc s ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs] at hnorm
    have habs : |τ - (τ - ε)| = ε := by
      rw [show τ - (τ - ε) = ε by ring, abs_of_pos hεpos]
    rwa [habs] at hnorm
  have key : ε⁻¹ * (∫ s in (τ - ε)..τ, Φ ε s) - c
      = ε⁻¹ * ((∫ s in (τ - ε)..τ, Φ ε s) - ε * c) := by
    field_simp
  rw [Real.dist_eq, key, abs_mul, abs_of_pos (inv_pos.mpr hεpos), hsub]
  calc ε⁻¹ * |∫ s in (τ - ε)..τ, (Φ ε s - c)| ≤ ε⁻¹ * ((η / 2) * ε) := by
        exact mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = η / 2 := by field_simp
    _ < η := by linarith

theorem solution
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hg : Continuous (Function.uncurry M.g))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T) (huτ : ContinuousAt u τ)
    (v : EuclideanSpace ℝ (Fin m))
    (y : ℝ → ℝ → EuclideanSpace ℝ (Fin n)) (K : ℝ)
    (hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn (y ε) (Set.Icc (τ - ε) τ) ∧
        ∀ s ∈ Set.Icc (τ - ε) τ, ‖y ε s - x τ‖ ≤ K * ε) :
    Tendsto
      (fun ε => ε⁻¹ * ((∫ s in (τ - ε)..τ, M.g (y ε s) v) -
        ∫ s in (τ - ε)..τ, M.g (x s) (u s)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (M.g (x τ) v - M.g (x τ) (u τ))) := by
  classical
  obtain ⟨huU, ⟨hubdd, Fu, hucont⟩, hxcont, hx0eq, Fx, hxderiv⟩ := hadm
  have hτT : τ ≤ M.T := hτ.2.le
  have h0τ : (0 : ℝ) < τ := hτ.1
  obtain ⟨cu0, hcu0⟩ := hubdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin m))
  set cu : ℝ := max cu0 0 with hcudef
  have hcu : ∀ t ∈ Icc (0 : ℝ) M.T, ‖u t‖ ≤ cu := by
    intro t ht
    have hmem : u t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) cu0 :=
      hcu0 (mem_image_of_mem u ht)
    rw [mem_closedBall_zero_iff] at hmem
    exact hmem.trans (le_max_left _ _)
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < τ := by
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h0τ)
  have hwin : ∀ ε : ℝ, ε < τ → 0 < ε → Icc (τ - ε) τ ⊆ Icc (0 : ℝ) M.T := by
    intro ε hετ hεpos s hs
    exact ⟨by linarith [hs.1], hs.2.trans hτT⟩
  -- the perturbed integrand
  have hgv : Continuous (fun z : EuclideanSpace ℝ (Fin n) => M.g z v) :=
    hg.comp (continuous_id.prodMk continuous_const)
  have hA : Tendsto (fun ε => ε⁻¹ * ∫ s in (τ - ε)..τ, M.g (y ε s) v)
      (𝓝[>] (0 : ℝ)) (𝓝 (M.g (x τ) v)) := by
    refine window_average_tendsto ?_ ?_
    · filter_upwards [hy, self_mem_nhdsWithin] with ε hyε hεp
      have hεpos : (0 : ℝ) < ε := hεp
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by linarith : τ - ε ≤ τ)]
      exact hgv.comp_continuousOn hyε.1
    · intro η hη
      obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp hgv.continuousAt η hη
      have hKtend : Tendsto (fun ε : ℝ => max K 0 * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc : Tendsto (fun ε : ℝ => max K 0 * ε) (𝓝 (0 : ℝ)) (𝓝 (max K 0 * 0)) :=
          (continuous_const.mul continuous_id).tendsto (0 : ℝ)
        rw [mul_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      filter_upwards [hy, hKtend.eventually_lt_const hδ, self_mem_nhdsWithin] with ε hyε hKε hεp
      intro s hs
      have hεpos : (0 : ℝ) < ε := hεp
      have h1 : ‖y ε s - x τ‖ ≤ K * ε := hyε.2 s hs
      have h2 : K * ε ≤ max K 0 * ε :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hεpos.le
      have h3 : dist (y ε s) (x τ) < δ := by
        rw [dist_eq_norm]
        linarith
      have := hδb h3
      rw [Real.dist_eq] at this
      exact this.le
  -- the base integrand
  have hxAt : ContinuousAt x τ := hxcont.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
  have hcomp : ContinuousAt (fun s => M.g (x s) (u s)) τ :=
    hg.continuousAt.comp (hxAt.prodMk huτ)
  have hB : Tendsto (fun ε => ε⁻¹ * ∫ s in (τ - ε)..τ, M.g (x s) (u s))
      (𝓝[>] (0 : ℝ)) (𝓝 (M.g (x τ) (u τ))) := by
    refine window_average_tendsto ?_ ?_
    · filter_upwards [hlt, self_mem_nhdsWithin] with ε hετ hεp
      have hεpos : (0 : ℝ) < ε := hεp
      have hsub := hwin ε hετ hεpos
      exact intervalIntegrable_comp_bounded (by linarith : τ - ε ≤ τ) hg
        (hxcont.mono hsub)
        (aestronglyMeasurable_of_continuousOn_diff_finset u Fu
          (hucont.mono (fun s hs => ⟨hsub hs.1, hs.2⟩)))
        (fun s hs => hcu s (hsub hs))
    · intro η hη
      obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp hcomp η hη
      have hεδ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
      filter_upwards [hεδ] with ε hε
      intro s hs
      have h3 : dist s τ < δ := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2])]
        linarith [hs.1]
      have := hδb h3
      rw [Real.dist_eq] at this
      exact this.le
  refine Tendsto.congr (fun ε => ?_) (hA.sub hB)
  rw [mul_sub]
