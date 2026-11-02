-- Prove2me | solution 1 for BilevelSOC.SecondOrder.c2_secondOrder
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:28:11.197327+00:00
-- url     : https://prove2.me/submissions/6ddcabf2-724d-4b07-99ef-806b7b2b5399

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology
open BilevelSOC.SecondOrder Filter Set

/-- Second-order Taylor expansion with uniform Peano remainder for a `C²` function. -/
theorem bsoc_taylor2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (hθ : ContDiff ℝ 2 θ) (x : V) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : V, ‖h‖ < δ →
      |θ (x + h) - θ x - fderiv ℝ θ x h - (1 / 2) * fderiv ℝ (fderiv ℝ θ) x h h|
        ≤ ε * ‖h‖ ^ 2 := by
  intro ε hε
  set B := fderiv ℝ (fderiv ℝ θ) x with hB
  have hC1 : ContDiff ℝ 1 (fderiv ℝ θ) := hθ.fderiv_right (m := 1) (by norm_num)
  have hdiff : ∀ y, HasFDerivAt θ (fderiv ℝ θ y) y := fun y =>
    ((hθ.differentiable (by norm_num)) y).hasFDerivAt
  have hB' : HasFDerivAt (fderiv ℝ θ) B x :=
    ((hC1.differentiable (by norm_num)) x).hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at hB'
  have := hB' hε
  rcases Metric.eventually_nhds_iff.1 this with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun h hh => ?_⟩
  -- one-dimensional auxiliary function
  let φ : ℝ → ℝ := fun s => θ (x + s • h) - s * fderiv ℝ θ x h - s ^ 2 / 2 * B h h
  let φ' : ℝ → ℝ := fun s => fderiv ℝ θ (x + s • h) h - fderiv ℝ θ x h - s * B h h
  have hφ : ∀ s, HasDerivAt φ (φ' s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add x
    have h2 : HasDerivAt (fun s => θ (x + s • h)) (fderiv ℝ θ (x + s • h) h) s :=
      (hdiff _).comp_hasDerivAt s h1
    have h3 : HasDerivAt (fun s : ℝ => s * fderiv ℝ θ x h) (fderiv ℝ θ x h) s := by
      simpa using (hasDerivAt_id s).mul_const (fderiv ℝ θ x h)
    have h4 : HasDerivAt (fun s : ℝ => s ^ 2 / 2 * B h h) (s * B h h) s := by
      exact (((hasDerivAt_pow 2 s).div_const 2).mul_const (B h h)).congr_deriv (by
        norm_num)
    exact (h2.sub h3).sub h4
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖φ' s‖ ≤ ε * ‖h‖ ^ 2 := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2.le
    have hsh : ‖s • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg hs0]
      calc s * ‖h‖ ≤ 1 * ‖h‖ := by gcongr
        _ = ‖h‖ := one_mul _
    have hin : dist (s • h) 0 < δ := by rw [dist_zero_right]; exact lt_of_le_of_lt hsh hh
    have key := hball hin
    have heq : φ' s = (fderiv ℝ θ (x + s • h) - fderiv ℝ θ x - B (s • h)) h := by
      simp only [φ', ContinuousLinearMap.sub_apply, map_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
    rw [heq]
    calc ‖(fderiv ℝ θ (x + s • h) - fderiv ℝ θ x - B (s • h)) h‖
        ≤ ‖fderiv ℝ θ (x + s • h) - fderiv ℝ θ x - B (s • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε * ‖s • h‖) * ‖h‖ := by gcongr
      _ ≤ (ε * ‖h‖) * ‖h‖ := by gcongr
      _ = ε * ‖h‖ ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := φ)
    (fun s _ => (hφ s).hasDerivWithinAt) hbound
  have e1 : φ 1 - φ 0 = θ (x + h) - θ x - fderiv ℝ θ x h - (1 / 2) * B h h := by
    simp only [φ, one_smul, zero_smul, add_zero]; ring
  rw [e1, Real.norm_eq_abs] at hmv
  exact hmv

/-- Second-order expansion along a curve `x + t d + (t²/2) w(t)` with `t w(t) → 0`. -/
theorem bsoc_curve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (hθ : ContDiff ℝ 2 θ) (x d : V) (w : ℝ → V)
    (hw : Tendsto (fun t : ℝ => t • w t) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |θ (x + t • d + (t ^ 2 / 2) • w t) - θ x - t * fderiv ℝ θ x d -
        (t ^ 2 / 2) * (fderiv ℝ θ x (w t) + fderiv ℝ (fderiv ℝ θ) x d d)| ≤ ε * t ^ 2 := by
  intro ε hε
  set B := fderiv ℝ (fderiv ℝ θ) x with hB
  set u : ℝ → V := fun t => (1 / 2 : ℝ) • (t • w t) with hu
  have hu0 : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hw.const_smul (1 / 2 : ℝ)
    simpa [u] using this
  have hv : Tendsto (fun t => d + u t) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    simpa using hu0.const_add d
  have hBc : Continuous (fun v : V => B v v) := by fun_prop
  have hBv : Tendsto (fun t => B (d + u t) (d + u t)) (𝓝[>] (0 : ℝ)) (𝓝 (B d d)) :=
    (hBc.tendsto d).comp hv
  set K := (‖d‖ + 1) ^ 2 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨δ, hδ, hT⟩ := bsoc_taylor2 θ hθ x (ε / 2 / K) (by positivity)
  -- eventually ‖u t‖ ≤ 1
  have ev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖u t‖ < 1 := by
    exact (hu0.norm).eventually (Iio_mem_nhds (by simp : ‖(0 : V)‖ < 1))
  have ev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), |B (d + u t) (d + u t) - B d d| < ε := by
    have := (hBv.sub_const (B d d))
    rw [sub_self] at this
    have := this.abs
    rw [abs_zero] at this
    exact this.eventually (gt_mem_nhds hε)
  have ev3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * (‖d‖ + 1) < δ := by
    have : Tendsto (fun t : ℝ => t * (‖d‖ + 1)) (𝓝[>] (0 : ℝ)) (𝓝 (0 * (‖d‖ + 1))) :=
      ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hδ)
  have ev4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [ev1, ev2, ev3, ev4] with t h1 h2 h3 h4
  have hh : t • d + (t ^ 2 / 2) • w t = t • (d + u t) := by
    simp only [u, smul_add, smul_smul]; congr 1; congr 1; ring
  have hnorm : ‖t • (d + u t)‖ ≤ t * (‖d‖ + 1) := by
    rw [norm_smul, Real.norm_of_nonneg h4.le]
    gcongr
    calc ‖d + u t‖ ≤ ‖d‖ + ‖u t‖ := norm_add_le _ _
      _ ≤ ‖d‖ + 1 := by linarith
  have hT' := hT (t • (d + u t)) (lt_of_le_of_lt hnorm h3)
  rw [add_assoc, hh]
  have hlin : fderiv ℝ θ x (t • (d + u t)) = t * fderiv ℝ θ x d +
      (t ^ 2 / 2) * fderiv ℝ θ x (w t) := by
    simp only [u, map_smul, map_add, smul_eq_mul]; ring
  have hquad : B (t • (d + u t)) (t • (d + u t)) = t ^ 2 * B (d + u t) (d + u t) := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  rw [hlin, hquad] at hT'
  have hn2 : ‖t • (d + u t)‖ ^ 2 ≤ t ^ 2 * K := by
    calc ‖t • (d + u t)‖ ^ 2 ≤ (t * (‖d‖ + 1)) ^ 2 := by gcongr
      _ = t ^ 2 * K := by rw [hK]; ring
  have hA : ε / 2 / K * ‖t • (d + u t)‖ ^ 2 ≤ ε / 2 * t ^ 2 := by
    calc ε / 2 / K * ‖t • (d + u t)‖ ^ 2 ≤ ε / 2 / K * (t ^ 2 * K) := by gcongr
      _ = ε / 2 * t ^ 2 := by field_simp
  have hB2 : |t ^ 2 / 2 * (B (d + u t) (d + u t) - B d d)| ≤ ε / 2 * t ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    nlinarith [h2.le, sq_nonneg t]
  have := abs_add_le (θ (x + t • (d + u t)) - θ x - (t * fderiv ℝ θ x d +
      t ^ 2 / 2 * fderiv ℝ θ x (w t)) - 1 / 2 * (t ^ 2 * B (d + u t) (d + u t)))
    (t ^ 2 / 2 * (B (d + u t) (d + u t) - B d d))
  have e : θ (x + t • (d + u t)) - θ x - (t * fderiv ℝ θ x d +
      t ^ 2 / 2 * fderiv ℝ θ x (w t)) - 1 / 2 * (t ^ 2 * B (d + u t) (d + u t)) +
      t ^ 2 / 2 * (B (d + u t) (d + u t) - B d d) =
      θ (x + t • (d + u t)) - θ x - t * fderiv ℝ θ x d -
        t ^ 2 / 2 * (fderiv ℝ θ x (w t) + B d d) := by ring
  rw [e] at this
  linarith

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (θ : V → ℝ) (hθ : ContDiff ℝ 2 θ) (x : V) :
    SecondOrderDirDiff θ x (fun d => fderiv ℝ θ x d)
      (fun d w => fderiv ℝ θ x w + fderiv ℝ (fderiv ℝ θ) x d d) ∧
    SecondOrderEpiRegular θ x (fun d => fderiv ℝ θ x d)
      (fun d w => fderiv ℝ θ x w + fderiv ℝ (fderiv ℝ θ) x d d) := by
  have hdiff : ∀ y, HasFDerivAt θ (fderiv ℝ θ y) y := fun y =>
    ((hθ.differentiable (by norm_num)) y).hasFDerivAt
  refine ⟨fun d => ⟨?_, fun w => ?_⟩, fun d w hw ε hε => ?_⟩
  · -- first-order directional derivative
    have h1 : HasDerivAt (fun s : ℝ => x + s • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    have h2 : HasDerivAt (fun s : ℝ => θ (x + s • d)) (fderiv ℝ θ x d) 0 := by
      exact (hdiff x).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    have := h2.tendsto_slope_zero_right
    unfold HasDirDerivAt
    refine this.congr' ?_
    filter_upwards with t
    simp [smul_eq_mul, div_eq_inv_mul]
  · -- second-order directional derivative
    have hw : Tendsto (fun t : ℝ => t • (fun _ : ℝ => w) t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t • w) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) • w)) :=
        (continuous_id.smul continuous_const).tendsto 0
      rw [zero_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hev := bsoc_curve θ hθ x d (fun _ => w) hw (ε / 4) (by positivity)
    have ev4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    filter_upwards [hev, ev4] with t h ht
    rw [Real.dist_eq]
    have ht2 : 0 < t ^ 2 / 2 := by positivity
    have e : (θ (x + t • d + (t ^ 2 / 2) • w) - θ x - t * fderiv ℝ θ x d) / (t ^ 2 / 2) -
        (fderiv ℝ θ x w + fderiv ℝ (fderiv ℝ θ) x d d) =
        (θ (x + t • d + (t ^ 2 / 2) • w) - θ x - t * fderiv ℝ θ x d -
          (t ^ 2 / 2) * (fderiv ℝ θ x w + fderiv ℝ (fderiv ℝ θ) x d d)) / (t ^ 2 / 2) := by
      field_simp
    rw [e, abs_div, abs_of_pos ht2, div_lt_iff₀ ht2]
    have : ε / 4 * t ^ 2 < ε * (t ^ 2 / 2) := by nlinarith [sq_pos_of_pos ht]
    linarith
  · -- epi-regularity
    have hev := bsoc_curve θ hθ x d w hw ε hε
    filter_upwards [hev] with t h
    have := (abs_le.1 h).1
    linarith
