-- Prove2me | solution 1 for FreeSamples.FullRevenue.theorem_1a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T11:23:27.280654+00:00
-- url     : https://prove2.me/submissions/e5831a60-cf96-411c-a39f-74166e073e5d

import Mathlib
import Definitions.Def_FreeSamples_FullRevenue_Policies

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FreeSamples.FullRevenue.Proof92068

open FreeSamples.FullRevenue

lemma isProb_N (m v : ℝ) : IsProbabilityMeasure (Revenue.N m v) := by
  unfold Revenue.N; infer_instance

attribute [local instance] isProb_N

/-! ## Part 1 -/

lemma part1 (u : ℝ → ℝ → ℝ) (hu : WellDefined u) (m v : ℝ) (hv : 0 < v) :
    bayesRisk u m v < ⊤ := by
  obtain ⟨a, ha, -⟩ := hu.attained m v hv
  exact lt_of_le_of_lt (iInf_le _ a) ha

/-! ## C1 Gaussian conjugacy -/

lemma postMean_eq (n m v h y : ℝ) :
    Revenue.postMean n m v h y =
      Revenue.postVar n v h * m / v + Revenue.postVar n v h / n * y := by
  unfold Revenue.postMean; ring

lemma postVar_pos (n v h : ℝ) (hn : 0 < n) (hv : 0 < v) (hh : 0 ≤ h) :
    0 < Revenue.postVar n v h := by
  unfold Revenue.postVar
  have : 0 < v * h + n := by nlinarith [mul_nonneg hv.le hh]
  positivity

lemma continuous_postMean (n m v h : ℝ) : Continuous (fun y => Revenue.postMean n m v h y) := by
  simp only [postMean_eq]; fun_prop

lemma measurable_g (n m v h : ℝ) :
    Measurable (fun q : ℝ × ℝ => Revenue.postMean n m v h q.1 + q.2) := by
  simp only [postMean_eq]; fun_prop

lemma N_post_eq (n m v h y : ℝ) :
    Revenue.N (Revenue.postMean n m v h y) (Revenue.postVar n v h) =
      (Revenue.N 0 (Revenue.postVar n v h)).map (Revenue.postMean n m v h y + ·) := by
  unfold Revenue.N; rw [gaussianReal_map_const_add, zero_add]

lemma prod_law (n m v h : ℝ) (hn : 0 < n) (hv : 0 < v) (hh : 0 ≤ h) :
    ((Revenue.N (m * h) (v * h ^ 2 + n * h)).prod (Revenue.N 0 (Revenue.postVar n v h))).map
      (fun q : ℝ × ℝ => Revenue.postMean n m v h q.1 + q.2) = Revenue.N m v := by
  have hs0 : 0 ≤ Revenue.postVar n v h := (postVar_pos n v h hn hv hh).le
  have hV : 0 ≤ v * h ^ 2 + n * h := by
    have := mul_nonneg hn.le hh; have := mul_nonneg hv.le (sq_nonneg h); linarith
  set s := Revenue.postVar n v h with hs
  set c := s * m / v with hc
  set d := s / n with hd
  have hg : (fun q : ℝ × ℝ => Revenue.postMean n m v h q.1 + q.2)
      = (fun q : ℝ × ℝ => q.1 + q.2) ∘ Prod.map (fun y => d * y + c) id := by
    funext q; simp only [Function.comp, Prod.map, postMean_eq, id]; rw [← hs]; ring
  rw [hg, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
  have h1 : (Revenue.N (m * h) (v * h ^ 2 + n * h)).map (fun y => d * y + c) =
      gaussianReal (d * (m * h) + c) (NNReal.mk (d ^ 2) (sq_nonneg _) * (v * h ^ 2 + n * h).toNNReal) := by
    have : (fun y => d * y + c) = (· + c) ∘ (d * ·) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop)]
    unfold Revenue.N
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
  rw [h1]
  change (gaussianReal _ _) ∗ (gaussianReal 0 s.toNNReal) = _
  rw [gaussianReal_conv_gaussianReal]
  unfold Revenue.N
  have hpos : 0 < v * h + n := by nlinarith [mul_nonneg hv.le hh]
  congr 1
  · rw [hc, hd, hs]; unfold Revenue.postVar; field_simp <;> ring
  · apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hV,
      Real.coe_toNNReal _ hs0, Real.coe_toNNReal _ hv.le]
    rw [hd, hs]; unfold Revenue.postVar; field_simp <;> ring

lemma lintegral_conj (n m v h : ℝ) (hn : 0 < n) (hv : 0 < v) (hh : 0 ≤ h)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ y, (∫⁻ x, φ x ∂(Revenue.N (Revenue.postMean n m v h y) (Revenue.postVar n v h)))
        ∂(Revenue.N (m * h) (v * h ^ 2 + n * h))
      = ∫⁻ x, φ x ∂(Revenue.N m v) := by
  rw [← prod_law n m v h hn hv hh, lintegral_map hφ (measurable_g n m v h),
    lintegral_prod (fun q : ℝ × ℝ => φ (Revenue.postMean n m v h q.1 + q.2))
      (hφ.comp (measurable_g n m v h)).aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [N_post_eq, lintegral_map hφ (by fun_prop)]

lemma integral_conj (n m v h : ℝ) (hn : 0 < n) (hv : 0 < v) (hh : 0 ≤ h)
    (F : ℝ → ℝ) (hFm : Measurable F) (hF : Integrable F (Revenue.N m v)) :
    Integrable (fun y => ∫ x, F x ∂(Revenue.N (Revenue.postMean n m v h y) (Revenue.postVar n v h)))
        (Revenue.N (m * h) (v * h ^ 2 + n * h)) ∧
    ∫ y, (∫ x, F x ∂(Revenue.N (Revenue.postMean n m v h y) (Revenue.postVar n v h)))
        ∂(Revenue.N (m * h) (v * h ^ 2 + n * h)) = ∫ x, F x ∂(Revenue.N m v) := by
  have hgm := measurable_g n m v h
  have hF' := hF
  rw [← prod_law n m v h hn hv hh] at hF'
  have hQ := (integrable_map_measure hF'.1 hgm.aemeasurable).1 hF'
  have hfun : (fun y => ∫ x, F x ∂(Revenue.N (Revenue.postMean n m v h y) (Revenue.postVar n v h)))
      = fun y => ∫ z, (F ∘ fun q : ℝ × ℝ => Revenue.postMean n m v h q.1 + q.2) (y, z)
          ∂(Revenue.N 0 (Revenue.postVar n v h)) := by
    funext y
    rw [N_post_eq, integral_map (by fun_prop) hFm.aestronglyMeasurable]
    rfl
  rw [hfun]
  refine ⟨hQ.integral_prod_left, ?_⟩
  rw [← integral_prod _ hQ]
  have hmap := integral_map
    (μ := (Revenue.N (m * h) (v * h ^ 2 + n * h)).prod (Revenue.N 0 (Revenue.postVar n v h)))
    hgm.aemeasurable hFm.aestronglyMeasurable
  rw [prod_law n m v h hn hv hh] at hmap
  exact hmap.symm

/-! ## C2 willingness to pay is at most the Bayes risk -/

lemma wtp_le_BR (u : ℝ → ℝ → ℝ) (hu : WellDefined u) (hA : Assumption1 u)
    (n m v : ℝ) (hn : 0 < n) (hv : 0 < v) (k : WithTop ℝ≥0) :
    willingnessToPay u n m v k ≤ BR u m v := by
  unfold willingnessToPay afterUtility
  split_ifs with hk
  · unfold U; linarith
  · dsimp only
    have hh0 := NNReal.coe_nonneg (k.untopD 0)
    generalize ((k.untopD 0 : ℝ≥0) : ℝ) = h at hh0 ⊢
    have hs := postVar_pos n v h hn hv hh0
    have contOf : ∀ G : ℝ → ℝ → ℝ, TwiceDifferentiable G →
        Continuous (fun y => G (Revenue.postMean n m v h y) (Revenue.postVar n v h)) := by
      intro G hG
      exact hG.1.comp_continuous ((continuous_postMean n m v h).prodMk continuous_const)
        (fun y => ⟨Set.mem_univ _, hs⟩)
    obtain ⟨a, ha, -⟩ := hu.attained m v hv
    have hBRint : Integrable (fun y => BR u (Revenue.postMean n m v h y) (Revenue.postVar n v h))
        (Revenue.N (m * h) (v * h ^ 2 + n * h)) := by
      refine ⟨(contOf _ hA.2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal
        (f := fun y => BR u (Revenue.postMean n m v h y) (Revenue.postVar n v h))
        (Filter.Eventually.of_forall fun y => by simp only [Pi.zero_apply]; exact ENNReal.toReal_nonneg)]
      calc ∫⁻ y, ENNReal.ofReal (BR u (Revenue.postMean n m v h y) (Revenue.postVar n v h))
              ∂(Revenue.N (m * h) (v * h ^ 2 + n * h))
            ≤ ∫⁻ y, actionLoss u (Revenue.postMean n m v h y) (Revenue.postVar n v h) a
              ∂(Revenue.N (m * h) (v * h ^ 2 + n * h)) := by
            refine lintegral_mono fun y => ?_
            unfold BR; exact ENNReal.ofReal_toReal_le.trans (iInf_le _ a)
        _ = actionLoss u m v a := by
            unfold actionLoss
            exact lintegral_conj n m v h hn hv hh0 _
              (hu.measurable_maximum.sub (hu.measurable_action a)).ennreal_ofReal
        _ < ⊤ := ha
    obtain ⟨hFint, hFeq⟩ := integral_conj n m v h hn hv hh0 (maximumUtility u)
      hu.measurable_maximum (hu.integrable_maximum m v hv)
    unfold U fullUtility
    rw [integral_sub hFint hBRint, hFeq]
    have := integral_nonneg (μ := Revenue.N (m * h) (v * h ^ 2 + n * h))
      (f := fun y => BR u (Revenue.postMean n m v h y) (Revenue.postVar n v h))
      (fun y => ENNReal.toReal_nonneg)
    linarith

lemma payment_le_BR (u : ℝ → ℝ → ℝ) (hu : WellDefined u) (hA : Assumption1 u)
    (n m v : ℝ) (hn : 0 < n) (hv : 0 < v) (k : WithTop ℝ≥0) (q : ℝ≥0) :
    payment u n m v k q ≤ BR u m v := by
  unfold payment; split_ifs with hq
  · exact hq.trans (wtp_le_BR u hu hA n m v hn hv k)
  · exact ENNReal.toReal_nonneg

/-! ## Part 3 upper bound for one-round offers -/

lemma oneRound_le (p : Revenue.Params) (u : ℝ → ℝ → ℝ) (hu : WellDefined u)
    (hA : Assumption1 u) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (π : PolicyData Ω) (h0 : ∀ᵐ ω ∂P, π.stop ω = 0) :
    expectedRevenue p u P θ B π ≤ ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) := by
  unfold expectedRevenue
  calc ∫⁻ ω, ENNReal.ofReal (realizedRevenue p u θ B π ω) ∂P
        ≤ ∫⁻ _ω, ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [h0, hB.eval_zero_ae_eq_zero] with ω hω hB0
          refine ENNReal.ofReal_le_ofReal ?_
          have hn := p.σsq_pos
          have hv := p.σ₀sq_pos
          have hpm : posteriorMean p θ B 0 ω = p.θ₀ := by
            simp only [posteriorMean, Revenue.Params.buyerMean, Revenue.postMean, Revenue.Y,
              Revenue.postVar, hB0, NNReal.coe_zero]
            field_simp <;> ring
          have hbv : p.buyerVar 0 = p.σ₀sq := by
            simp only [Revenue.Params.buyerVar, Revenue.postVar]
            field_simp <;> ring
          have key : realizedRevenue p u θ B π ω = payment u p.σsq (posteriorMean p θ B 0 ω)
              (p.buyerVar 0) (π.allocation ω) (π.price ω) := by
            simp [realizedRevenue, hω]
          rw [key, hpm, hbv]
          exact payment_le_BR u hu hA _ _ _ hn hv _ _
    _ = ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) := by
          rw [lintegral_const, measure_univ, mul_one]

/-! ## Part 4, P1: one-sided Peano Taylor bound -/

lemma peano_lower (f : ℝ × ℝ → ℝ) (z0 : ℝ × ℝ) (hz0 : 0 < z0.2)
    (hd : ∀ z : ℝ × ℝ, 0 < z.2 → DifferentiableAt ℝ f z)
    (hdd : DifferentiableAt ℝ (fderiv ℝ f) z0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ d : ℝ × ℝ, ‖d‖ < δ →
      f z0 + fderiv ℝ f z0 d + (1 / 2) * fderiv ℝ (fderiv ℝ f) z0 d d - ε * ‖d‖ ^ 2
        ≤ f (z0 + d) := by
  have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdd.hasFDerivAt).def hε
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.eventually_nhds_iff.1 ho
  refine ⟨min δ1 z0.2, lt_min hδ1 hz0, fun d hd' => ?_⟩
  have hdδ1 : ‖d‖ < δ1 := lt_of_lt_of_le hd' (min_le_left _ _)
  have hdz : ‖d‖ < z0.2 := lt_of_lt_of_le hd' (min_le_right _ _)
  have hd2 : |d.2| ≤ ‖d‖ := by
    have := norm_snd_le d; rwa [Real.norm_eq_abs] at this
  have hpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < (z0 + t • d).2 := by
    intro t ht
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have h1 : |t * d.2| ≤ ‖d‖ := by
      rw [abs_mul, abs_of_nonneg ht.1]
      calc t * |d.2| ≤ 1 * |d.2| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
        _ ≤ ‖d‖ := by linarith
    have := neg_abs_le (t * d.2)
    linarith
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => f (z0 + t • d) - f z0 - t * fderiv ℝ f z0 d
          - t ^ 2 / 2 * fderiv ℝ (fderiv ℝ f) z0 d d)
        (fderiv ℝ f (z0 + t • d) d - fderiv ℝ f z0 d - t * fderiv ℝ (fderiv ℝ f) z0 d d)
        (Set.Icc 0 1) t := by
    intro t ht
    have hc : HasDerivAt (fun t : ℝ => z0 + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add z0
    have h1 : HasDerivAt (fun t => f (z0 + t • d)) (fderiv ℝ f (z0 + t • d) d) t :=
      (hd _ (hpos t ht)).hasFDerivAt.comp_hasDerivAt t hc
    have h2 : HasDerivAt (fun t : ℝ => t * fderiv ℝ f z0 d) (fderiv ℝ f z0 d) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ f z0 d)
    have h3 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * fderiv ℝ (fderiv ℝ f) z0 d d)
        (t * fderiv ℝ (fderiv ℝ f) z0 d d) t := by
      have hh := ((hasDerivAt_id t).mul (hasDerivAt_id t)).mul_const
        (fderiv ℝ (fderiv ℝ f) z0 d d / 2)
      have e : (fun t : ℝ => t ^ 2 / 2 * fderiv ℝ (fderiv ℝ f) z0 d d) =
          fun x => id x * id x * (fderiv ℝ (fderiv ℝ f) z0 d d / 2) := by
        funext x; simp only [id]; ring
      rw [e]
      exact hh.congr_deriv (show (1 * t + t * 1) * (fderiv ℝ (fderiv ℝ f) z0 d d / 2) =
        t * fderiv ℝ (fderiv ℝ f) z0 d d by ring)
    exact (((h1.sub_const (f z0)).sub h2).sub h3).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖fderiv ℝ f (z0 + t • d) d - fderiv ℝ f z0 d - t * fderiv ℝ (fderiv ℝ f) z0 d d‖
        ≤ ε * ‖d‖ ^ 2 := by
    intro t ht
    have htd : ‖t • d‖ ≤ ‖d‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖d‖ ≤ 1 * ‖d‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
        _ = ‖d‖ := one_mul _
    have hmem : dist (t • d) 0 < δ1 := by rw [dist_zero_right]; linarith
    have key := hδ1' hmem
    have heq : fderiv ℝ f (z0 + t • d) d - fderiv ℝ f z0 d - t * fderiv ℝ (fderiv ℝ f) z0 d d
        = (fderiv ℝ f (z0 + t • d) - fderiv ℝ f z0 - fderiv ℝ (fderiv ℝ f) z0 (t • d)) d := by
      simp only [ContinuousLinearMap.sub_apply, map_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
    rw [heq]
    calc ‖(fderiv ℝ f (z0 + t • d) - fderiv ℝ f z0 - fderiv ℝ (fderiv ℝ f) z0 (t • d)) d‖
          ≤ ‖fderiv ℝ f (z0 + t • d) - fderiv ℝ f z0 - fderiv ℝ (fderiv ℝ f) z0 (t • d)‖ * ‖d‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε * ‖t • d‖) * ‖d‖ := mul_le_mul_of_nonneg_right key (norm_nonneg _)
      _ ≤ (ε * ‖d‖) * ‖d‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htd hε.le) (norm_nonneg _)
      _ = ε * ‖d‖ ^ 2 := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    ⟨zero_le_one, le_rfl⟩
  simp only [zero_smul, add_zero, sub_self, zero_mul, one_smul, one_mul, sub_zero,
    Real.norm_eq_abs, mul_one] at hmvt
  have := neg_abs_le (f (z0 + d) - f z0 - fderiv ℝ f z0 d - 1 ^ 2 / 2 * fderiv ℝ (fderiv ℝ f) z0 d d)
  norm_num at this hmvt ⊢
  linarith

/-! ## P2: coordinates of the first and second derivative -/

lemma clm_decomp (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1:ℝ), (0:ℝ)) + b • ((0:ℝ), (1:ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

lemma clm2_decomp (L2 : ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    L2 (a, b) (a, b) = a ^ 2 * L2 (1, 0) (1, 0)
      + a * b * (L2 (1, 0) (0, 1) + L2 (0, 1) (1, 0)) + b ^ 2 * L2 (0, 1) (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1:ℝ), (0:ℝ)) + b • ((0:ℝ), (1:ℝ)) := by
    ext <;> simp
  rw [this]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

lemma partials (F : ℝ → ℝ → ℝ) (θ₀ v : ℝ) (hv : 0 < v)
    (hd : ∀ z : ℝ × ℝ, 0 < z.2 → DifferentiableAt ℝ (Function.uncurry F) z)
    (hdd : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry F)) (θ₀, v)) :
    Revenue.dθ F θ₀ v = fderiv ℝ (Function.uncurry F) (θ₀, v) (1, 0) ∧
    Revenue.dv F θ₀ v = fderiv ℝ (Function.uncurry F) (θ₀, v) (0, 1) ∧
    Revenue.dθθ F θ₀ v = fderiv ℝ (fderiv ℝ (Function.uncurry F)) (θ₀, v) (1, 0) (1, 0) := by
  have hx : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((x, v) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x :=
    fun x => (hasDerivAt_id x).prodMk (hasDerivAt_const x v)
  have hy : HasDerivAt (fun w : ℝ => ((θ₀, w) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) v :=
    (hasDerivAt_const v θ₀).prodMk (hasDerivAt_id v)
  have hpx : ∀ x, deriv (fun y => F y v) x =
      fderiv ℝ (Function.uncurry F) (x, v) (1, 0) := fun x => by
    have hh := (hd (x, v) hv).hasFDerivAt.comp_hasDerivAt x (hx x)
    exact hh.deriv
  have hpy := (hd (θ₀, v) hv).hasFDerivAt.comp_hasDerivAt v hy
  refine ⟨hpx θ₀, hpy.deriv, ?_⟩
  unfold Revenue.dθθ
  simp_rw [hpx]
  have h1 := hdd.hasFDerivAt.comp_hasDerivAt θ₀ (hx θ₀)
  have h2 := h1.clm_apply (hasDerivAt_const θ₀ ((1 : ℝ), (0 : ℝ)))
  simpa using h2.deriv

/-! ## P3: global quartic lower bound -/

lemma quartic_lower (F : ℝ → ℝ) (α β γ δ : ℝ) (hδ : 0 < δ) (hF0 : ∀ a, 0 ≤ F a)
    (hF : ∀ a, |a| < δ → α + β * a + γ * a ^ 2 ≤ F a) (a : ℝ) :
    α + β * a + γ * a ^ 2 - (|α| / δ ^ 4 + |β| / δ ^ 3 + |γ| / δ ^ 2) * a ^ 4 ≤ F a := by
  have hK : 0 ≤ |α| / δ ^ 4 + |β| / δ ^ 3 + |γ| / δ ^ 2 := by positivity
  have ha4 : (0:ℝ) ≤ a ^ 4 := by positivity
  rcases lt_or_ge |a| δ with ha | ha
  · have := hF a ha
    nlinarith [mul_nonneg hK ha4]
  · obtain ⟨t, ht⟩ : ∃ t, t = |a| := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact lt_of_lt_of_le hδ ha
    have h4 : a ^ 4 = t ^ 4 := by rw [ht]; exact (Even.pow_abs ⟨2, rfl⟩ a).symm
    have h2 : a ^ 2 = t ^ 2 := by rw [ht]; exact (sq_abs a).symm
    obtain ⟨r, hr⟩ : ∃ r, r = t / δ := ⟨_, rfl⟩
    have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hδ]; rw [ht]; linarith
    have htr : t = r * δ := by rw [hr]; field_simp
    have e1 : |α| / δ ^ 4 * t ^ 4 = |α| * r ^ 4 := by rw [htr]; field_simp <;> ring
    have e2 : |β| / δ ^ 3 * t ^ 4 = |β| * t * r ^ 3 := by rw [htr]; field_simp <;> ring
    have e3 : |γ| / δ ^ 2 * t ^ 4 = |γ| * t ^ 2 * r ^ 2 := by rw [htr]; field_simp <;> ring
    have r2 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
    have r3 : 1 ≤ r ^ 3 := one_le_pow₀ hr1
    have r4 : 1 ≤ r ^ 4 := one_le_pow₀ hr1
    have b1 : α ≤ |α| := le_abs_self α
    have b2 : β * a ≤ |β| * t := by rw [ht, ← abs_mul]; exact le_abs_self _
    have b3 : γ * a ^ 2 ≤ |γ| * t ^ 2 := by
      rw [h2]; exact mul_le_mul_of_nonneg_right (le_abs_self γ) (by positivity)
    have := hF0 a
    rw [h4, add_mul, add_mul, e1, e2, e3]
    nlinarith [mul_le_mul_of_nonneg_left r4 (abs_nonneg α),
      mul_le_mul_of_nonneg_left r3 (mul_nonneg (abs_nonneg β) ht0.le),
      mul_le_mul_of_nonneg_left r2 (mul_nonneg (abs_nonneg γ) (sq_nonneg t))]

/-! ## P4: Gaussian polynomial lower bound -/

lemma int_pow_gauss (μ : ℝ) (s : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal μ s) := by
  have h := (memLp_id_gaussianReal' (μ := μ) (v := s) (k : ℝ≥0∞)
    (ENNReal.natCast_ne_top k)).integrable_norm_pow'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [norm_pow]

lemma integral_poly (μ : ℝ) (s : ℝ≥0) (c0 c1 c2 c4 : ℝ) :
    ∫ y, (c0 + c1 * y + c2 * y ^ 2 - c4 * y ^ 4) ∂(gaussianReal μ s) =
      c0 + c1 * (∫ y, y ∂(gaussianReal μ s)) + c2 * (∫ y, y ^ 2 ∂(gaussianReal μ s))
        - c4 * (∫ y, y ^ 4 ∂(gaussianReal μ s)) := by
  have h1 : Integrable (fun y : ℝ => c1 * y) (gaussianReal μ s) := by
    simpa using (int_pow_gauss μ s 1).const_mul c1
  have hA0 : Integrable (fun y : ℝ => c0 + c1 * y) (gaussianReal μ s) := (integrable_const c0).add h1
  have h2 : Integrable (fun y : ℝ => c2 * y ^ 2) (gaussianReal μ s) := (int_pow_gauss μ s 2).const_mul c2
  have h4 : Integrable (fun y : ℝ => c4 * y ^ 4) (gaussianReal μ s) := (int_pow_gauss μ s 4).const_mul c4
  have hA : Integrable (fun y : ℝ => c0 + c1 * y + c2 * y ^ 2) (gaussianReal μ s) := hA0.add h2
  rw [integral_sub hA h4, integral_add hA0 h2,
    integral_add (integrable_const c0) h1, integral_const, integral_const_mul,
    integral_const_mul, integral_const_mul]
  simp

lemma integrable_poly (μ : ℝ) (s : ℝ≥0) (c0 c1 c2 c4 : ℝ) :
    Integrable (fun y : ℝ => c0 + c1 * y + c2 * y ^ 2 - c4 * y ^ 4) (gaussianReal μ s) := by
  have h1 : Integrable (fun y : ℝ => c1 * y) (gaussianReal μ s) := by
    simpa using (int_pow_gauss μ s 1).const_mul c1
  exact (((integrable_const c0).add h1).add ((int_pow_gauss μ s 2).const_mul c2)).sub
    ((int_pow_gauss μ s 4).const_mul c4)

lemma gauss_lower (e : ℝ) (s : ℝ≥0) (α β γ K : ℝ) (hK : 0 ≤ K) :
    α + β * e + γ * (e ^ 2 + s) - K * (8 * e ^ 4 + 8 * (s : ℝ) ^ 2 * ∫ z, z ^ 4 ∂(gaussianReal 0 1))
      ≤ ∫ y, (α + β * y + γ * y ^ 2 - K * y ^ 4) ∂(gaussianReal e s) := by
  have hP := integrable_poly e s α β γ K
  have hrep : gaussianReal e s = (gaussianReal 0 1).map (fun z => e + Real.sqrt s * z) := by
    have : (fun z : ℝ => e + Real.sqrt s * z) = (fun z => z + e) ∘ (fun z => Real.sqrt s * z) := by
      funext z; simp only [Function.comp]; ring
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1
    · simp
    · apply NNReal.eq; simp [Real.sq_sqrt (NNReal.coe_nonneg s)]
  rw [hrep] at hP
  have hcomp := (integrable_map_measure hP.1 (by fun_prop)).1 hP
  rw [hrep, integral_map (by fun_prop) hP.1]
  have hz1 : ∫ z, z ∂(gaussianReal (0:ℝ) 1) = 0 := integral_id_gaussianReal
  have hz2 : ∫ z, z ^ 2 ∂(gaussianReal (0:ℝ) 1) = 1 := by
    have := variance_of_integral_eq_zero (X := id) (μ := gaussianReal (0:ℝ) 1) aemeasurable_id hz1
    rw [variance_id_gaussianReal] at this
    simpa using this.symm
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt s := ⟨_, rfl⟩
  rw [← hr] at hcomp ⊢
  have hr2 : r ^ 2 = s := by rw [hr]; exact Real.sq_sqrt (NNReal.coe_nonneg s)
  have hr4 : r ^ 4 = (s : ℝ) ^ 2 := by rw [← hr2]; ring
  have hpt : ∀ z : ℝ, (α + β * e + γ * e ^ 2 - 8 * K * e ^ 4) + (β * r + 2 * γ * e * r) * z
      + (γ * r ^ 2) * z ^ 2 - (8 * K * r ^ 4) * z ^ 4
      ≤ α + β * (e + r * z) + γ * (e + r * z) ^ 2 - K * (e + r * z) ^ 4 := by
    intro z
    have h8 : (e + r * z) ^ 4 ≤ 8 * e ^ 4 + 8 * r ^ 4 * z ^ 4 := by
      nlinarith [sq_nonneg (e - r * z), sq_nonneg (e + r * z), sq_nonneg (e ^ 2 - (r * z) ^ 2),
        sq_nonneg (e * r * z), sq_nonneg (e ^ 2 + (r * z) ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_left h8 hK]
  have hcomp' : Integrable (fun z => α + β * (e + r * z) + γ * (e + r * z) ^ 2
      - K * (e + r * z) ^ 4) (gaussianReal 0 1) := hcomp
  have hmono := integral_mono (integrable_poly 0 1 _ _ _ _) hcomp' hpt
  rw [integral_poly, hz1, hz2] at hmono
  have hc4 := integral_nonneg (μ := gaussianReal (0:ℝ) 1) (f := fun z : ℝ => z ^ 4)
    (fun z => by positivity)
  rw [hr4] at hmono
  rw [hr2] at hmono
  nlinarith [hmono]

/-! ## P5: law of the posterior-mean displacement at a constant time -/

lemma law_A (p : Revenue.Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B) (h : ℝ≥0) :
    P.map (fun ω => posteriorMean p θ B h ω - p.θ₀) =
      gaussianReal (p.σ₀sq / (p.σ₀sq * h + p.σsq) * h * p.μb)
        (⟨(p.σ₀sq / (p.σ₀sq * h + p.σsq) * h) ^ 2, sq_nonneg _⟩ * p.σssq.toNNReal
          + ⟨(p.σ₀sq / (p.σ₀sq * h + p.σsq) * Real.sqrt p.σsq) ^ 2, sq_nonneg _⟩ * h) := by
  have hn := p.σsq_pos
  have hv := p.σ₀sq_pos
  have hθm := hM.meas_θ
  have hBm := hM.meas_B h
  have hpos : 0 < p.σ₀sq * (h : ℝ) + p.σsq := by nlinarith [mul_nonneg hv.le h.2]
  obtain ⟨k, hk⟩ : ∃ k, k = p.σ₀sq / (p.σ₀sq * h + p.σsq) := ⟨_, rfl⟩
  rw [← hk]
  have hfun : (fun ω => posteriorMean p θ B h ω - p.θ₀) =
      (fun ω => (k * h) * (θ ω - p.θ₀)) + (fun ω => (k * Real.sqrt p.σsq) * B h ω) := by
    funext ω
    simp only [Pi.add_apply, posteriorMean, Revenue.Params.buyerMean, Revenue.postMean,
      Revenue.postVar, Revenue.Y, hk]
    field_simp
    ring
  rw [hfun]
  have hX : P.map (fun ω => (k * h) * (θ ω - p.θ₀)) =
      gaussianReal (k * h * p.μb) (⟨(k * h) ^ 2, sq_nonneg _⟩ * p.σssq.toNNReal) := by
    have : (fun ω => (k * h) * (θ ω - p.θ₀)) = ((k * h) * ·) ∘ (· - p.θ₀) ∘ θ := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) hM.meas_θ, hM.law_θ]
    unfold Revenue.N
    rw [gaussianReal_map_sub_const, gaussianReal_map_const_mul]
    congr 1; ring
  have hY : P.map (fun ω => (k * Real.sqrt p.σsq) * B h ω) =
      gaussianReal 0 (⟨(k * Real.sqrt p.σsq) ^ 2, sq_nonneg _⟩ * h) := by
    have : (fun ω => (k * Real.sqrt p.σsq) * B h ω) = ((k * Real.sqrt p.σsq) * ·) ∘ B h := rfl
    rw [this, ← Measure.map_map (by fun_prop) (hM.meas_B h),
      (hM.brownian.hasLaw_eval h).map_eq, gaussianReal_map_const_mul, mul_zero]
    rfl
  have hind : IndepFun (fun ω => (k * h) * (θ ω - p.θ₀))
      (fun ω => (k * Real.sqrt p.σsq) * B h ω) P := by
    have := hM.indep.comp (φ := fun x => (k * h) * (x - p.θ₀))
      (ψ := fun b : ℝ≥0 → ℝ => (k * Real.sqrt p.σsq) * b h) (by fun_prop) (by fun_prop)
    exact this
  rw [gaussianReal_add_gaussianReal_of_indepFun hind hX hY, add_zero]

/-! ## P7: the constant-time full-sale policy -/

noncomputable def constPolicy (p : Revenue.Params) (u : ℝ → ℝ → ℝ) {Ω : Type*} (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) : PolicyData Ω :=
  ⟨fun _ => (h : WithTop ℝ≥0), fun _ => ⊤,
    fun ω => (BR u (posteriorMean p θ B h ω) (p.buyerVar h)).toNNReal⟩

lemma constPolicy_spec (p : Revenue.Params) (u : ℝ → ℝ → ℝ) (hA : Assumption1 u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B) (h : ℝ≥0) :
    IsAdmissible (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B)
      (constPolicy p u θ B h) ∧
    ∀ ω, realizedRevenue p u θ B (constPolicy p u θ B h) ω =
      BR u (posteriorMean p θ B h ω) (p.buyerVar h) := by
  have hs : 0 < p.buyerVar h := postVar_pos _ _ _ p.σsq_pos p.σ₀sq_pos h.2
  have hg : Continuous (fun y => BR u (Revenue.postMean p.σsq p.θ₀ p.σ₀sq h y) (p.buyerVar h)) :=
    hA.2.1.comp_continuous ((continuous_postMean _ _ _ _).prodMk continuous_const)
      (fun y => ⟨Set.mem_univ _, hs⟩)
  constructor
  · have hT : IsStoppingTime (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B)
        (constPolicy p u θ B h).stop := isStoppingTime_const _ h
    have hms : hT.measurableSpace = Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B h :=
      IsStoppingTime.measurableSpace_const _ h
    refine ⟨hT, ?_, ?_⟩
    · rw [hms]
      have hY : Measurable[Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B h]
          (Revenue.Y p.σsq θ B h) := by
        unfold Revenue.dataFiltration
        exact (Filtration.stronglyAdapted_natural (β := fun _ => ℝ) _ h).measurable
      exact measurable_real_toNNReal.comp (hg.measurable.comp hY)
    · exact measurable_const
  · intro ω
    have hBR : 0 ≤ BR u (posteriorMean p θ B h ω) (p.buyerVar h) := ENNReal.toReal_nonneg
    have hW : willingnessToPay u p.σsq (posteriorMean p θ B h ω) (p.buyerVar h) ⊤ =
        BR u (posteriorMean p θ B h ω) (p.buyerVar h) := by
      simp only [willingnessToPay, afterUtility, if_true, U]; ring
    have hne : (constPolicy p u θ B h).stop ω ≠ ⊤ := WithTop.coe_ne_top
    unfold realizedRevenue
    rw [if_neg hne]
    show payment u p.σsq (posteriorMean p θ B h ω) (p.buyerVar h) ⊤
      (BR u (posteriorMean p θ B h ω) (p.buyerVar h)).toNNReal = _
    unfold payment
    rw [hW, Real.coe_toNNReal _ hBR, if_pos le_rfl]

/-! ## P6a: revenue of the constant-time policy is at least the Gaussian polynomial bound -/

lemma ofReal_integral_le' {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  calc ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part fun x => le_max_left _ _)
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part
          (Filter.Eventually.of_forall fun x => (le_max_right (f x) 0 : (0:ℝ) ≤ max (f x) 0))
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := lintegral_mono fun x =>
        ENNReal.ofReal_le_ofReal_iff'.2 ((le_total 0 (f x)).imp
          (fun h => (max_eq_left h).le) (fun h => (max_eq_right h).le))

lemma revenue_ge (p : Revenue.Params) (u : ℝ → ℝ → ℝ) (hA : Assumption1 u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B) (h : ℝ≥0) (e : ℝ) (s : ℝ≥0)
    (hlaw : P.map (fun ω => posteriorMean p θ B h ω - p.θ₀) = gaussianReal e s)
    (α β γ K : ℝ) (hK : 0 ≤ K)
    (hpoly : ∀ a, α + β * a + γ * a ^ 2 - K * a ^ 4 ≤ BR u (p.θ₀ + a) (p.buyerVar h)) :
    ENNReal.ofReal (α + β * e + γ * (e ^ 2 + s)
        - K * (8 * e ^ 4 + 8 * (s : ℝ) ^ 2 * ∫ z, z ^ 4 ∂(gaussianReal 0 1)))
      ≤ expectedRevenue p u P θ B (constPolicy p u θ B h) := by
  calc _ ≤ ENNReal.ofReal (∫ y, (α + β * y + γ * y ^ 2 - K * y ^ 4) ∂(gaussianReal e s)) :=
        ENNReal.ofReal_le_ofReal (gauss_lower e s α β γ K hK)
    _ ≤ ∫⁻ y, ENNReal.ofReal (α + β * y + γ * y ^ 2 - K * y ^ 4) ∂(gaussianReal e s) :=
        ofReal_integral_le' _ _ (integrable_poly e s α β γ K)
    _ = ∫⁻ y, ENNReal.ofReal (α + β * y + γ * y ^ 2 - K * y ^ 4)
          ∂(P.map (fun ω => posteriorMean p θ B h ω - p.θ₀)) := by rw [hlaw]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (α + β * (posteriorMean p θ B h ω - p.θ₀)
          + γ * (posteriorMean p θ B h ω - p.θ₀) ^ 2
          - K * (posteriorMean p θ B h ω - p.θ₀) ^ 4) ∂P :=
        lintegral_map_le (fun y => ENNReal.ofReal (α + β * y + γ * y ^ 2 - K * y ^ 4))
          (fun ω => posteriorMean p θ B h ω - p.θ₀)
    _ ≤ ∫⁻ ω, ENNReal.ofReal (realizedRevenue p u θ B (constPolicy p u θ B h) ω) ∂P := by
        refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
        rw [(constPolicy_spec p u hA P θ B hM h).2 ω]
        have := hpoly (posteriorMean p θ B h ω - p.θ₀)
        have e1 : p.θ₀ + (posteriorMean p θ B h ω - p.θ₀) = posteriorMean p θ B h ω := by ring
        rw [e1] at this
        exact this
    _ = expectedRevenue p u P θ B (constPolicy p u θ B h) := rfl

lemma law_A' (p : Revenue.Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B) (h : ℝ≥0) :
    ∃ s : ℝ≥0, P.map (fun ω => posteriorMean p θ B h ω - p.θ₀) =
        gaussianReal (p.σ₀sq / (p.σ₀sq * h + p.σsq) * h * p.μb) s ∧
      (s : ℝ) = (p.σ₀sq / (p.σ₀sq * h + p.σsq)) ^ 2
        * ((h : ℝ) ^ 2 * (p.σssq.toNNReal : ℝ) + p.σsq * h) := by
  refine ⟨_, law_A p P θ B hM h, ?_⟩
  change (p.σ₀sq / (p.σ₀sq * h + p.σsq) * h) ^ 2 * (p.σssq.toNNReal : ℝ)
    + (p.σ₀sq / (p.σ₀sq * h + p.σsq) * Real.sqrt p.σsq) ^ 2 * (h : ℝ) = _
  simp only [mul_pow, Real.sq_sqrt p.σsq_pos.le]
  ring

/-! ## P6b: a small constant sampling time beats the immediate offer -/

lemma part4 (p : Revenue.Params) (u : ℝ → ℝ → ℝ) (hA : Assumption1 u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B)
    (hpositive : 0 < Revenue.drift (BR u) p.θ₀ p.σ₀sq p.μb) :
    ∃ π : PolicyData Ω,
      IsAdmissible (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) π ∧
      ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) < expectedRevenue p u P θ B π := by
  have hn := p.σsq_pos
  have hv := p.σ₀sq_pos
  have hd : ∀ z : ℝ × ℝ, 0 < z.2 → DifferentiableAt ℝ (Function.uncurry (BR u)) z :=
    fun z hz => (hA.2.2 z hz).1
  have hdd := (hA.2.2 (p.θ₀, p.σ₀sq) hv).2
  obtain ⟨hθ, hvd, hθθ⟩ := partials (BR u) p.θ₀ p.σ₀sq hv hd hdd
  have hDdef : Revenue.drift (BR u) p.θ₀ p.σ₀sq p.μb =
      1 / 2 * Revenue.dθθ (BR u) p.θ₀ p.σ₀sq - Revenue.dv (BR u) p.θ₀ p.σ₀sq
        + p.μb / p.σ₀sq * Revenue.dθ (BR u) p.θ₀ p.σ₀sq := rfl
  generalize hD : Revenue.drift (BR u) p.θ₀ p.σ₀sq p.μb = D at hpositive hDdef
  generalize hA1 : Revenue.dθ (BR u) p.θ₀ p.σ₀sq = A1 at hθ hDdef
  generalize hA2 : Revenue.dv (BR u) p.θ₀ p.σ₀sq = A2 at hvd hDdef
  generalize hA11 : Revenue.dθθ (BR u) p.θ₀ p.σ₀sq = A11 at hθθ hDdef
  have hε : 0 < D / 2 := by linarith
  obtain ⟨δ, hδ, hpe⟩ :=
    peano_lower (Function.uncurry (BR u)) (p.θ₀, p.σ₀sq) hv hd hdd (D / 2) hε
  obtain ⟨X, hX⟩ : ∃ X, fderiv ℝ (fderiv ℝ (Function.uncurry (BR u))) (p.θ₀, p.σ₀sq) (1, 0) (0, 1)
      + fderiv ℝ (fderiv ℝ (Function.uncurry (BR u))) (p.θ₀, p.σ₀sq) (0, 1) (1, 0) = X :=
    ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y,
      fderiv ℝ (fderiv ℝ (Function.uncurry (BR u))) (p.θ₀, p.σ₀sq) (0, 1) (0, 1) = Y :=
    ⟨_, rfl⟩
  have hBR0 : 0 ≤ BR u p.θ₀ p.σ₀sq := ENNReal.toReal_nonneg
  -- the one-sided second-order window bound
  have hwin : ∀ a b : ℝ, |a| < δ → |b| < δ →
      BR u p.θ₀ p.σ₀sq + b * A2 + (1 / 2 * Y - D / 2) * b ^ 2 + (A1 + 1 / 2 * b * X) * a
        + (1 / 2 * A11 - D / 2) * a ^ 2 ≤ BR u (p.θ₀ + a) (p.σ₀sq + b) := by
    intro a b ha hb
    have hnorm : ‖((a, b) : ℝ × ℝ)‖ < δ := by
      rw [Prod.norm_def]
      exact max_lt (by simpa using ha) (by simpa using hb)
    have hn2 : ‖((a, b) : ℝ × ℝ)‖ ^ 2 ≤ a ^ 2 + b ^ 2 := by
      rw [Prod.norm_def]
      simp only [Real.norm_eq_abs]
      rcases le_total |a| |b| with hab | hab
      · rw [max_eq_right hab, sq_abs]; nlinarith [sq_nonneg a]
      · rw [max_eq_left hab, sq_abs]; nlinarith [sq_nonneg b]
    have key := hpe (a, b) hnorm
    rw [clm2_decomp (fderiv ℝ (fderiv ℝ (Function.uncurry (BR u))) (p.θ₀, p.σ₀sq)) a b,
      clm_decomp (fderiv ℝ (Function.uncurry (BR u)) (p.θ₀, p.σ₀sq)) a b,
      ← hθ, ← hvd, ← hθθ, hX, hY] at key
    simp only [Prod.mk_add_mk, Function.uncurry_apply_pair] at key
    nlinarith [mul_le_mul_of_nonneg_left hn2 hε.le]
  -- explicit coefficient functions of the sampling time t
  obtain ⟨k, hkt⟩ : ∃ k : ℝ → ℝ, ∀ t, k t = p.σ₀sq / (p.σ₀sq * t + p.σsq) :=
    ⟨_, fun _ => rfl⟩
  have hk : ContinuousAt k 0 := by
    have : k = fun t => p.σ₀sq / (p.σ₀sq * t + p.σsq) := funext hkt
    rw [this]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by rw [mul_zero, zero_add]; exact hn.ne')
  have hkpos : ∀ t, 0 ≤ t → 0 < k t := by
    intro t ht
    rw [hkt]
    have : 0 < p.σ₀sq * t + p.σsq := by nlinarith [mul_nonneg hv.le ht]
    positivity
  obtain ⟨bf, hbf⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = -p.σ₀sq * k t * t := ⟨_, fun _ => rfl⟩
  obtain ⟨αf, hαf⟩ : ∃ f : ℝ → ℝ, ∀ t,
      f t = BR u p.θ₀ p.σ₀sq + bf t * A2 + (1 / 2 * Y - D / 2) * bf t ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨βf, hβf⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = A1 + 1 / 2 * bf t * X := ⟨_, fun _ => rfl⟩
  obtain ⟨Kf, hKf⟩ : ∃ f : ℝ → ℝ, ∀ t,
      f t = |αf t| / δ ^ 4 + |βf t| / δ ^ 3 + |1 / 2 * A11 - D / 2| / δ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, ((p.σssq.toNNReal : ℝ≥0) : ℝ) = W := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ c : ℝ, (∫ z, z ^ 4 ∂(gaussianReal (0:ℝ) 1)) = c := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = -p.σ₀sq * k t * A2
      + (1 / 2 * Y - D / 2) * p.σ₀sq ^ 2 * k t ^ 2 * t
      + (A1 - 1 / 2 * p.σ₀sq * k t * t * X) * k t * p.μb
      + (1 / 2 * A11 - D / 2) * (k t ^ 2 * t * p.μb ^ 2 + k t ^ 2 * (t * W + p.σsq))
      - Kf t * (8 * k t ^ 4 * p.μb ^ 4 * t ^ 3 + 8 * k t ^ 4 * (t * W + p.σsq) ^ 2 * t * c4) :=
    ⟨_, fun _ => rfl⟩
  have hbc : ContinuousAt bf 0 := by rw [show bf = _ from funext hbf]; fun_prop
  have hαc : ContinuousAt αf 0 := by rw [show αf = _ from funext hαf]; fun_prop
  have hβc : ContinuousAt βf 0 := by rw [show βf = _ from funext hβf]; fun_prop
  have hKc : ContinuousAt Kf 0 := by
    rw [show Kf = _ from funext hKf]
    exact (((continuous_abs.continuousAt.comp hαc).div_const _).add
      ((continuous_abs.continuousAt.comp hβc).div_const _)).add continuousAt_const
  have hΨc : ContinuousAt Ψ 0 := by rw [show Ψ = _ from funext hΨ]; fun_prop
  have hΨ0 : 0 < Ψ 0 := by
    have e0 : Ψ 0 = p.σ₀sq ^ 2 / p.σsq * (D / 2) := by
      rw [hΨ, hkt, hDdef]
      field_simp
      ring
    rw [e0]
    exact mul_pos (by positivity) hε
  have hL : ∀ t, αf t + βf t * (k t * t * p.μb)
      + (1 / 2 * A11 - D / 2) * ((k t * t * p.μb) ^ 2 + k t ^ 2 * (t ^ 2 * W + p.σsq * t))
      - Kf t * (8 * (k t * t * p.μb) ^ 4
        + 8 * (k t ^ 2 * (t ^ 2 * W + p.σsq * t)) ^ 2 * c4)
      = BR u p.θ₀ p.σ₀sq + t * Ψ t := by
    intro t
    rw [hαf, hβf, hΨ, hbf]
    ring
  -- choose a small positive sampling time
  have hbc' : ContinuousAt (fun t => p.σ₀sq * k t * t) 0 := by fun_prop
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (0 < Ψ t ∧ p.σ₀sq * k t * t < δ) ∧ t ∈ Set.Ioi (0:ℝ) := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    refine (hΨc.eventually (lt_mem_nhds hΨ0)).and (hbc'.eventually (gt_mem_nhds ?_))
    simp only [mul_zero]
    exact hδ
  obtain ⟨t, ⟨hΨt, hbt⟩, ht⟩ := hev.exists
  have ht' : 0 < t := ht
  obtain ⟨h, hht⟩ : ∃ h : ℝ≥0, (h : ℝ) = t := ⟨⟨t, ht'.le⟩, rfl⟩
  have hbv : p.buyerVar h = p.σ₀sq + bf t := by
    rw [hbf, hkt]
    simp only [Revenue.Params.buyerVar, Revenue.postVar]
    rw [hht]
    have : 0 < p.σ₀sq * t + p.σsq := by nlinarith [mul_nonneg hv.le ht'.le]
    field_simp
    ring
  have hbabs : |bf t| < δ := by
    rw [hbf, show -p.σ₀sq * k t * t = -(p.σ₀sq * k t * t) by ring, abs_neg,
      abs_of_nonneg (by have := hkpos t ht'.le; positivity)]
    exact hbt
  have hpoly : ∀ a, αf t + βf t * a + (1 / 2 * A11 - D / 2) * a ^ 2 - Kf t * a ^ 4
      ≤ BR u (p.θ₀ + a) (p.buyerVar h) := by
    intro a
    rw [hKf]
    refine quartic_lower (fun a => BR u (p.θ₀ + a) (p.buyerVar h)) (αf t) (βf t)
      (1 / 2 * A11 - D / 2) δ hδ (fun a => ENNReal.toReal_nonneg) (fun a ha => ?_) a
    show _ ≤ BR u (p.θ₀ + a) (p.buyerVar h)
    have := hwin a (bf t) ha hbabs
    rw [← hbv] at this
    rw [hαf, hβf]
    linarith
  have hK0 : 0 ≤ Kf t := by rw [hKf]; positivity
  obtain ⟨s', hlaw, hs'⟩ := law_A' p P θ B hM h
  rw [hht, ← hkt] at hlaw
  rw [hht, ← hkt, hW] at hs'
  have hrev := revenue_ge p u hA P θ B hM h _ s' hlaw (αf t) (βf t) (1 / 2 * A11 - D / 2)
    (Kf t) hK0 hpoly
  rw [hs', hc4] at hrev
  refine ⟨constPolicy p u θ B h, (constPolicy_spec p u hA P θ B hM h).1,
    lt_of_lt_of_le ?_ ((congrArg ENNReal.ofReal (hL t).symm).trans_le hrev)⟩
  have hpos : 0 < t * Ψ t := mul_pos ht' hΨt
  rw [ENNReal.ofReal_lt_ofReal_iff']
  exact ⟨by linarith, by linarith⟩

end FreeSamples.FullRevenue.Proof92068

open MeasureTheory ProbabilityTheory ENNReal NNReal FreeSamples FreeSamples.FullRevenue in
theorem solution (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    (hu : WellDefined u) (hA : Assumption1 u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (p.θ₀ + p.μb) p.σssq θ B)
    (hpositive : 0 < Revenue.drift (BR u) p.θ₀ p.σ₀sq p.μb) :
    bayesRisk u p.θ₀ p.σ₀sq < ⊤ ∧
    ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) <
      optimalRevenue p u P θ B (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) ∧
    (∀ π : PolicyData Ω,
      IsOneRound P (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) π →
      expectedRevenue p u P θ B π ≤ ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) ∧
      expectedRevenue p u P θ B π <
        optimalRevenue p u P θ B (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B)) ∧
    ∃ π : PolicyData Ω,
      IsAdmissible (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) π ∧
      ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) < expectedRevenue p u P θ B π := by
  have h4 := Proof92068.part4 p u hA P θ B hM hpositive
  have h2 : ENNReal.ofReal (BR u p.θ₀ p.σ₀sq) <
      optimalRevenue p u P θ B (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) := by
    obtain ⟨π, hπ, hlt⟩ := h4
    refine lt_of_lt_of_le hlt ?_
    unfold optimalRevenue
    exact le_iSup₂ (f := fun π (_ : IsAdmissible
      (Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) π) => expectedRevenue p u P θ B π) π hπ
  have : IsProbabilityMeasure P := hM.isProb
  refine ⟨Proof92068.part1 u hu p.θ₀ p.σ₀sq p.σ₀sq_pos, h2, fun π hπ => ?_, h4⟩
  have h1 := Proof92068.oneRound_le p u hu hA P θ B hM.brownian.toIsPreBrownianReal π hπ.2
  exact ⟨h1, lt_of_le_of_lt h1 h2⟩
