-- Prove2me | solution 1 for BetaCoskew.ThreeMoment.eq_6_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T17:30:59.205664+00:00
-- url     : https://prove2.me/submissions/fc20d1a7-c8d3-4655-92e4-a84ec632c34a

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics BetaCoskew.ThreeMoment

/-- The cdf of the zero measure takes the value `1` at `1`: its rational pre-cdf is constant
in the rational argument, hence not a Stieltjes point, so the default cdf is used. -/
lemma bc_cdf_zero_one : cdf (0 : Measure ℝ) 1 = 1 := by
  have h1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  rw [← h1, cdf, Measure.prod_zero, condCDF, stieltjesOfMeasurableRat_eq]
  have hpre : ∀ r : ℚ, preCDF (0 : Measure (Unit × ℝ)) r = preCDF (0 : Measure (Unit × ℝ)) 0 := by
    intro r
    simp [preCDF, Measure.IicSnd]
  have hnot : ¬ IsRatStieltjesPoint (fun (a : Unit) (r : ℚ) =>
      (preCDF (0 : Measure (Unit × ℝ)) r a).toReal) () := by
    intro h
    have ht := h.tendsto_atTop_one
    have hb := h.tendsto_atBot_zero
    simp only [hpre] at ht hb
    have e1 := tendsto_nhds_unique ht tendsto_const_nhds
    have e2 := tendsto_nhds_unique hb tendsto_const_nhds
    rw [← e1] at e2
    norm_num at e2
  rw [toRatCDF, if_neg hnot, defaultRatCDF]
  norm_num

/-- A cdf with a continuous density `f` is differentiable with derivative `f`. -/
lemma bc_cdf_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hlaw : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) (x : ℝ) :
    HasDerivAt (cdf μ) (f x) x := by
  have hlint : (∫⁻ x, ENNReal.ofReal (f x)) = 1 := by
    have := measure_univ (μ := μ)
    rw [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  have hint : Integrable f := by
    refine ⟨hfc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0), hlint]
    exact ENNReal.one_lt_top
  have hcdf : ∀ y, cdf μ y = ∫ t in Set.Iic y, f t := by
    intro y
    rw [cdf_eq_real, measureReal_def, hlaw, withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
        (Eventually.of_forall hf0), ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Iic (fun t _ => hf0 t)
  have hcdf' : cdf μ = fun y => (∫ t in Set.Iic 0, f t) + ∫ t in (0:ℝ)..y, f t := by
    funext y
    rw [hcdf y, ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
    ring
  rw [hcdf']
  exact ((hfc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

/-- Second-order Taylor expansion from a derivative that is itself differentiable at the point. -/
lemma bc_taylor2 {G G1 : ℝ → ℝ} {a c : ℝ}
    (hG : ∀ᶠ y in 𝓝 a, HasDerivAt G (G1 y) y) (hG1 : HasDerivAt G1 c a) :
    (fun x : ℝ => G (a + x) - (G a + G1 a * x + c / 2 * x ^ 2)) =o[𝓝 0]
      (fun x : ℝ => x ^ 2) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hG
  set s : Set ℝ := Metric.ball 0 δ with hs
  have hderiv : ∀ x ∈ s, HasDerivWithinAt
      (fun x : ℝ => G (a + x) - (G a + G1 a * x + c / 2 * x ^ 2))
      (G1 (a + x) - G1 a - c * x) s x := by
    intro x hx
    have hx' : a + x ∈ Metric.ball a δ := by
      rw [Metric.mem_ball] at hx ⊢
      simpa [dist_eq_norm] using hx
    have h1 : HasDerivAt (fun x : ℝ => G (a + x)) (G1 (a + x)) x := by
      exact (hball (a + x) hx').comp_const_add a x
    have h2 : HasDerivAt (fun x : ℝ => G a + G1 a * x + c / 2 * x ^ 2)
        (G1 a + c * x) x := by
      have := (((hasDerivAt_id' x).const_mul (G1 a)).const_add (G a)).add
        ((hasDerivAt_pow 2 x).const_mul (c / 2))
      exact this.congr_deriv (by push_cast; ring)
    exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by ring)
  have hlo : (fun x : ℝ => G1 (a + x) - G1 a - c * x) =o[𝓝[s] 0]
      (fun x : ℝ => (x - 0) ^ 1) := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.mp hG1
    simp only [smul_eq_mul, sub_zero, pow_one] at this ⊢
    refine (this.congr (fun x => by ring) (fun x => rfl)).mono nhdsWithin_le_nhds
  have hmain := Convex.isLittleO_pow_succ_real (convex_ball 0 δ) (Metric.mem_ball_self hδ)
    hderiv hlo
  rw [(Metric.isOpen_ball).nhdsWithin_eq (Metric.mem_ball_self hδ)] at hmain
  simpa using hmain

/-- Chain rule for `y ↦ W1 (1 - F y) * U1 y` to second order at a point. -/
lemma bc_G_deriv {F f W1 W2 U1 U2 : ℝ → ℝ} {a f' w3 u3 : ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x) (hf : HasDerivAt f f' a)
    (hW1 : ∀ᶠ p in 𝓝 (1 - F a), HasDerivAt W1 (W2 p) p)
    (hW2 : HasDerivAt W2 w3 (1 - F a))
    (hU1 : ∀ᶠ y in 𝓝 a, HasDerivAt U1 (U2 y) y) (hU2 : HasDerivAt U2 u3 a) :
    (∀ᶠ y in 𝓝 a, HasDerivAt (fun y => W1 (1 - F y) * U1 y)
      (W2 (1 - F y) * (-f y) * U1 y + W1 (1 - F y) * U2 y) y) ∧
    HasDerivAt (fun y => W2 (1 - F y) * (-f y) * U1 y + W1 (1 - F y) * U2 y)
      (w3 * (-f a) * (-f a) * U1 a + W2 (1 - F a) * (-f') * U1 a +
        W2 (1 - F a) * (-f a) * U2 a +
        (W2 (1 - F a) * (-f a) * U2 a + W1 (1 - F a) * u3)) a := by
  have hFc : Tendsto (fun y => 1 - F y) (𝓝 a) (𝓝 (1 - F a)) :=
    ((hF a).continuousAt).const_sub 1
  constructor
  · filter_upwards [hFc.eventually hW1, hU1] with y hy1 hy2
    have hc : HasDerivAt (fun y => W1 (1 - F y)) (W2 (1 - F y) * (-f y)) y :=
      hy1.comp y ((hF y).const_sub 1)
    exact hc.mul hy2
  · have hW1a : HasDerivAt W1 (W2 (1 - F a)) (1 - F a) := hW1.self_of_nhds
    have hU1a : HasDerivAt U1 (U2 a) a := hU1.self_of_nhds
    have e1 : HasDerivAt (fun y => W2 (1 - F y)) (w3 * (-f a)) a :=
      hW2.comp a ((hF a).const_sub 1)
    have e2 : HasDerivAt (fun y => W1 (1 - F y)) (W2 (1 - F a) * (-f a)) a :=
      hW1a.comp a ((hF a).const_sub 1)
    have := ((e1.mul hf.neg).mul hU1a).add (e2.mul hU2)
    exact this.congr_deriv (by simp only [Pi.mul_apply, Pi.neg_apply]; ring)

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (u w : ℝ → ℝ) (rf : ℝ)
    (RM : Ω → ℝ) (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_smooth : ContDiff ℝ 1 f)
    (hf_law : P.map RM = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hF0 : 0 < cdf (P.map RM) 1) (hF1 : cdf (P.map RM) 1 < 1)
    (hu3 : ContDiffAt ℝ 3 u 1)
    (hw3 : ContDiffAt ℝ 3 w (1 - cdf (P.map RM) 1))
    (hrf : 0 < 1 + rf) (hK : kernelMean P u w RM ≠ 0) :
    premA P u w RM f = -(1 + rf) * deriv (mFun P u w rf RM) 1 ∧
    premB P u w RM f = -(1 + rf) * iteratedDeriv 2 (mFun P u w rf RM) 1 := by
  set F := cdf (P.map RM) with hFdef
  set p0 := 1 - F 1 with hp0
  have hRM : AEMeasurable RM P := by
    by_contra hnm
    rw [hFdef, Measure.map_of_not_aemeasurable hnm, bc_cdf_zero_one] at hF1
    exact lt_irrefl _ hF1
  have : IsProbabilityMeasure (P.map RM) := Measure.isProbabilityMeasure_map hRM
  have hF : ∀ x, HasDerivAt F (f x) x :=
    bc_cdf_hasDerivAt (P.map RM) f hf_nonneg hf_smooth.continuous hf_law
  have hf' : HasDerivAt f (deriv f 1) 1 :=
    ((hf_smooth.differentiable (by norm_num)) 1).hasDerivAt
  have hu2 : ContDiffAt ℝ 2 (deriv u) 1 := hu3.derivWithin (by norm_num)
  have hu1 : ContDiffAt ℝ 1 (deriv (deriv u)) 1 := hu2.derivWithin (by norm_num)
  have hU1 : ∀ᶠ y in 𝓝 (1 : ℝ), HasDerivAt (deriv u) (deriv (deriv u) y) y := by
    filter_upwards [hu2.eventually (by norm_num)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasDerivAt
  have hU2 : HasDerivAt (deriv (deriv u)) (deriv (deriv (deriv u)) 1) 1 :=
    (hu1.differentiableAt (by norm_num)).hasDerivAt
  have hw2 : ContDiffAt ℝ 2 (deriv w) p0 := hw3.derivWithin (by norm_num)
  have hw1 : ContDiffAt ℝ 1 (deriv (deriv w)) p0 := hw2.derivWithin (by norm_num)
  have hW1 : ∀ᶠ p in 𝓝 p0, HasDerivAt (deriv w) (deriv (deriv w) p) p := by
    filter_upwards [hw2.eventually (by norm_num)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasDerivAt
  have hW2 : HasDerivAt (deriv (deriv w)) (deriv (deriv (deriv w)) p0) p0 :=
    (hw1.differentiableAt (by norm_num)).hasDerivAt
  obtain ⟨hG, hG1⟩ := bc_G_deriv hF hf' hW1 hW2 hU1 hU2
  set D := (1 + rf) * kernelMean P u w RM with hD
  have hD0 : D ≠ 0 := mul_ne_zero hrf.ne' hK
  have hm : mFun P u w rf RM = fun y => deriv w (1 - F y) * deriv u y / D := by
    funext y; rfl
  have hmd : ∀ᶠ y in 𝓝 (1 : ℝ), deriv (mFun P u w rf RM) y =
      (deriv (deriv w) (1 - F y) * (-f y) * deriv u y +
        deriv w (1 - F y) * deriv (deriv u) y) / D := by
    filter_upwards [hG] with y hy
    rw [hm]
    exact (hy.div_const D).deriv
  have hd1 := hmd.self_of_nhds
  have hd2 : iteratedDeriv 2 (mFun P u w rf RM) 1 =
      (deriv (deriv (deriv w)) p0 * (-f 1) * (-f 1) * deriv u 1 +
        deriv (deriv w) p0 * (-deriv f 1) * deriv u 1 +
        deriv (deriv w) p0 * (-f 1) * deriv (deriv u) 1 +
        (deriv (deriv w) p0 * (-f 1) * deriv (deriv u) 1 +
          deriv w p0 * deriv (deriv (deriv u)) 1)) / D := by
    have hmd' : deriv (mFun P u w rf RM) =ᶠ[𝓝 (1 : ℝ)] fun y =>
        (deriv (deriv w) (1 - F y) * (-f y) * deriv u y +
          deriv w (1 - F y) * deriv (deriv u) y) / D := hmd
    rw [iteratedDeriv_succ, iteratedDeriv_one, hmd'.deriv_eq]
    exact (hG1.div_const D).deriv
  have h2 : iteratedDeriv 2 u = deriv (deriv u) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h3 : iteratedDeriv 3 u = deriv (deriv (deriv u)) := by
    rw [iteratedDeriv_succ, h2]
  have h2w : iteratedDeriv 2 w = deriv (deriv w) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h3w : iteratedDeriv 3 w = deriv (deriv (deriv w)) := by
    rw [iteratedDeriv_succ, h2w]
  constructor
  · rw [hd1, premA]
    simp only [h2, h2w]
    rw [← hFdef, ← hp0, hD]
    field_simp
    ring
  · rw [hd2, premB]
    simp only [h2, h3, h2w, h3w]
    rw [← hFdef, ← hp0, hD]
    field_simp
    ring
