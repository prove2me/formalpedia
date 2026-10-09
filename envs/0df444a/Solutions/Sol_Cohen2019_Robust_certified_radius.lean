-- Prove2me | solution 1 for Cohen2019.Robust.certified_radius
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:42:06.284098+00:00
-- url     : https://prove2.me/submissions/a809ef4a-a9ee-43a1-871b-69ddb37605e2

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

set_option autoImplicit false

/-! ### Phi facts (copied from our accepted siblings 9d2ea776 / 9c82c60e) -/

open MeasureTheory ProbabilityTheory in
theorem c3a_phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
  intro a b hab
  unfold Cohen2019.Robust.Phi
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h
    have h2 := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h2
    linarith
  have hm := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at hm
  rw [hm] at hpos
  have : ¬ (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ 0) := by
    intro hle; exact hpos (ENNReal.ofReal_eq_zero.mpr hle)
  linarith

open MeasureTheory ProbabilityTheory in
theorem c3a_phi_continuous : Continuous Cohen2019.Robust.Phi := by
  have hfun : Cohen2019.Robust.Phi = fun t => cdf (gaussianReal 0 1) t := rfl
  rw [hfun, continuous_iff_continuousAt]
  intro a
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [(monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  have hs := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hs
  have hle := (monotone_cdf (gaussianReal 0 1)).leftLim_le (le_refl a)
  linarith

open MeasureTheory ProbabilityTheory Filter in
theorem c3a_phi_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q) = q := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (Iio_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (Ioi_mem_nhds hq1)).exists
  have hmem : q ∈ Set.Icc (Cohen2019.Robust.Phi a) (Cohen2019.Robust.Phi b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ a b c3a_phi_continuous hmem
  have hS : {s : ℝ | q ≤ Cohen2019.Robust.Phi s} = Set.Ici t := by
    ext s
    simp only [Set.mem_Ici]
    rw [← ht]
    exact c3a_phi_strictMono.le_iff_le
  unfold Cohen2019.Robust.PhiInvReal
  rw [hS, csInf_Ici, ht]

open MeasureTheory ProbabilityTheory in
theorem c3a_phi_def (t : ℝ) :
    (gaussianReal 0 1).real (Set.Iic t) = Cohen2019.Robust.Phi t := by
  rw [Cohen2019.Robust.Phi, cdf_eq_real]

open MeasureTheory ProbabilityTheory in
theorem c3a_phi_neg (t : ℝ) : Cohen2019.Robust.Phi (-t) = 1 - Cohen2019.Robust.Phi t := by
  have h := gaussianReal_map_neg (μ := (0:ℝ)) (v := 1)
  rw [neg_zero] at h
  rw [← c3a_phi_def, ← c3a_phi_def]
  have h1 : (gaussianReal 0 1).real (Set.Iic (-t)) = (gaussianReal 0 1).real (Set.Ici t) := by
    conv_lhs => rw [← h]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext y
    simp
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [h1, ← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic]

theorem c3a_phiInv_one_sub {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.PhiInvReal (1 - q) = - Cohen2019.Robust.PhiInvReal q := by
  apply c3a_phi_strictMono.injective
  rw [c3a_phi_inv (by linarith) (by linarith), c3a_phi_neg, c3a_phi_inv hq0 hq1]

/-! ### Product Gaussian density (copied from our accepted sibling bd7edd52) -/

section dens

open MeasureTheory ProbabilityTheory

variable {N : ℕ}

noncomputable def c3a_gw (y : Fin N → ℝ) : ℝ := Real.exp (-(∑ i, y i ^ 2) / 2)

lemma c3a_prod_pdf (y : Fin N → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (y i) = (Real.sqrt (2 * Real.pi))⁻¹ ^ N * c3a_gw y := by
  simp only [gaussianPDFReal, c3a_gw, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

lemma c3a_pi_gauss_eq :
    Measure.pi (fun _ : Fin N => gaussianReal 0 1) =
      (volume : Measure (Fin N → ℝ)).withDensity
        (fun y => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) := by
  apply Measure.pi_eq
  intro s hs
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox]
  simp_rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    setIntegral_nonneg (hs i) fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  have hint : Integrable (fun y : Fin N → ℝ => ∏ i, gaussianPDFReal 0 1 (y i)) := by
    have := Integrable.fintype_prod (f := fun (_ : Fin N) (x : ℝ) => gaussianPDFReal 0 1 x)
      (μ := fun _ => volume) (fun _ => integrable_gaussianPDFReal 0 1)
    simpa [← volume_pi] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (ae_of_all _ fun y => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  rw [← integral_indicator hbox]
  have hind : (Set.univ.pi s).indicator (fun y : Fin N → ℝ => ∏ i, gaussianPDFReal 0 1 (y i)) =
      fun y => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (y i) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hy i trivial) _).symm
    · rw [Set.indicator_of_notMem hy]
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ s i := by simpa [Set.mem_pi] using hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_indicator (hs _)]

lemma c3a_integral_pi_gauss (g : (Fin N → ℝ) → ℝ) :
    ∫ y, g y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ N * ∫ y, c3a_gw y * g y := by
  have hm : Measurable (fun y : Fin N → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  rw [c3a_pi_gauss_eq, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    c3a_prod_pdf, smul_eq_mul, mul_assoc]

/-- Cameron–Martin shift formula for the standard Gaussian on `ℝᴺ`. -/
theorem c3a_cm (g : EuclideanSpace ℝ (Fin N) → ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    ∫ u, g (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) =
      ∫ u, g u * Real.exp (inner ℝ v u - ‖v‖ ^ 2 / 2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) := by
  rw [← map_pi_eq_stdGaussian]
  have he : (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) =
      ⇑(MeasurableEquiv.toLp 2 (Fin N → ℝ)) := rfl
  rw [he, integral_map_equiv, integral_map_equiv]
  rw [← he, c3a_integral_pi_gauss, c3a_integral_pi_gauss]
  congr 1
  set w : Fin N → ℝ := WithLp.ofLp v with hw
  have hv : v = WithLp.toLp 2 w := rfl
  have key : ∀ y : Fin N → ℝ, c3a_gw y * g (WithLp.toLp 2 y + v) =
      (fun z => c3a_gw (z - w) * g (WithLp.toLp 2 z)) (y + w) := by
    intro y
    simp only [add_sub_cancel_right, WithLp.toLp_add, hv]
  simp_rw [key]
  rw [integral_add_right_eq_self (fun z => c3a_gw (z - w) * g (WithLp.toLp 2 z)) w]
  congr 1
  funext y
  rw [mul_comm (g _), ← mul_assoc]
  congr 1
  rw [c3a_gw, c3a_gw, ← Real.exp_add, hv, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.real_norm_sq_eq]
  congr 1
  simp only [dotProduct, star_trivial, Pi.sub_apply, sub_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  try simp only [WithLp.ofLp_toLp, PiLp.toLp_apply]
  have : ∑ i, 2 * y i * w i = 2 * ∑ i, y i * w i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

end dens

/-! ### Gaussian marginals and Neyman–Pearson -/

section np

open MeasureTheory ProbabilityTheory

variable {N : ℕ}

theorem c3a_marg (e : EuclideanSpace ℝ (Fin N)) (he : ‖e‖ = 1) (c : ℝ) :
    ∫ u, ({u : EuclideanSpace ℝ (Fin N) | inner ℝ e u ≤ c}).indicator (fun _ => (1 : ℝ)) u
      ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) = Cohen2019.Robust.Phi c := by
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin N)) := innerSL ℝ e with hL
  have hLn : ‖L‖ = 1 := by rw [hL, innerSL_apply_norm, he]
  have hmapL : (stdGaussian (EuclideanSpace ℝ (Fin N))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hLn]
    simp
  have hset : {u : EuclideanSpace ℝ (Fin N) | inner ℝ e u ≤ c} = L ⁻¹' Set.Iic c := by
    ext u; simp [hL]
  have hSm : MeasurableSet {u : EuclideanSpace ℝ (Fin N) | inner ℝ e u ≤ c} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [integral_indicator hSm, setIntegral_const, smul_eq_mul, mul_one, hset,
    ← map_measureReal_apply L.continuous.measurable measurableSet_Iic, hmapL, c3a_phi_def]

theorem c3a_int_bdd (k : EuclideanSpace ℝ (Fin N) → ℝ) (hk : Measurable k)
    (h0 : ∀ u, 0 ≤ k u) (h1 : ∀ u, k u ≤ 1) :
    Integrable k (stdGaussian (EuclideanSpace ℝ (Fin N))) :=
  Integrable.of_bound hk.aestronglyMeasurable 1
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h0 u, h1 u])

theorem c3a_L_int (v : EuclideanSpace ℝ (Fin N)) :
    Integrable (fun u => Real.exp (inner ℝ v u - ‖v‖ ^ 2 / 2))
      (stdGaussian (EuclideanSpace ℝ (Fin N))) := by
  apply Integrable.of_integral_ne_zero
  have h := c3a_cm (fun _ => (1 : ℝ)) v
  simp only [one_mul] at h
  rw [← h]
  simp

/-- Neyman–Pearson lower bound (Cohen et al., Lemma 3/4 with half-space `A`). -/
theorem c3a_np (k : EuclideanSpace ℝ (Fin N) → ℝ) (hk : Measurable k)
    (h0 : ∀ u, 0 ≤ k u) (h1 : ∀ u, k u ≤ 1) (v : EuclideanSpace ℝ (Fin N)) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hA : p ≤ ∫ u, k u ∂(stdGaussian (EuclideanSpace ℝ (Fin N)))) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal p - ‖v‖) ≤
      ∫ u, k (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) := by
  by_cases hv : v = 0
  · subst hv
    simp only [norm_zero, sub_zero, add_zero]
    rw [c3a_phi_inv hp0 hp1]
    exact hA
  set γ := stdGaussian (EuclideanSpace ℝ (Fin N)) with hγ
  have ha : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set a := ‖v‖ with ha_def
  set e : EuclideanSpace ℝ (Fin N) := a⁻¹ • v with he_def
  have hen : ‖e‖ = 1 := norm_smul_inv_norm hv
  have hinner : ∀ u, inner ℝ v u = a * inner ℝ e u := by
    intro u
    rw [he_def, real_inner_smul_left]
    field_simp
  have hev : inner ℝ e v = a := by
    rw [he_def, real_inner_smul_left, real_inner_self_eq_norm_sq, ← ha_def]
    field_simp
  set s := Cohen2019.Robust.PhiInvReal p with hs
  set S : Set (EuclideanSpace ℝ (Fin N)) := {u | inner ℝ e u ≤ s} with hS_def
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  set χ : EuclideanSpace ℝ (Fin N) → ℝ := S.indicator (fun _ => (1 : ℝ)) with hχ
  have hχm : Measurable χ := measurable_const.indicator hSm
  have hχ0 : ∀ u, 0 ≤ χ u := fun u => Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hχ1 : ∀ u, χ u ≤ 1 := fun u => Set.indicator_le_self' (fun _ _ => zero_le_one) u
  have hSp : ∫ u, χ u ∂γ = p := by
    rw [hχ, hS_def, c3a_marg e hen s, hs, c3a_phi_inv hp0 hp1]
  have hSshift : ∫ u, χ (u + v) ∂γ = Cohen2019.Robust.Phi (s - a) := by
    have : (fun u => χ (u + v)) =
        ({u : EuclideanSpace ℝ (Fin N) | inner ℝ e u ≤ s - a}).indicator (fun _ => (1 : ℝ)) := by
      funext u
      simp only [hχ, hS_def, Set.indicator, Set.mem_ofPred_eq, inner_add_right, hev]
      congr 1
      apply propext
      constructor <;> intro h <;> linarith
    rw [this, c3a_marg e hen]
  set L : EuclideanSpace ℝ (Fin N) → ℝ := fun u => Real.exp (inner ℝ v u - a ^ 2 / 2) with hL
  set t : ℝ := Real.exp (a * s - a ^ 2 / 2) with ht
  have hLint : Integrable L γ := c3a_L_int v
  have hLm : Measurable L := by fun_prop
  have hLpos : ∀ u, 0 < L u := fun u => Real.exp_pos _
  have hkint := c3a_int_bdd k hk h0 h1
  have hχint := c3a_int_bdd χ hχm hχ0 hχ1
  have hcmk : ∫ u, k (u + v) ∂γ = ∫ u, k u * L u ∂γ := c3a_cm k v
  have hcmχ : ∫ u, χ (u + v) ∂γ = ∫ u, χ u * L u ∂γ := c3a_cm χ v
  have hkLint : Integrable (fun u => k u * L u) γ := by
    refine hLint.mono' (hk.mul hLm).aestronglyMeasurable (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 u) (hLpos u).le)]
    nlinarith [h1 u, hLpos u]
  have hχLint : Integrable (fun u => χ u * L u) γ := by
    refine hLint.mono' (hχm.mul hLm).aestronglyMeasurable (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ0 u) (hLpos u).le)]
    nlinarith [hχ1 u, hLpos u]
  have hpt : ∀ u, (k u - χ u) * t ≤ k u * L u - χ u * L u := by
    intro u
    by_cases hu : u ∈ S
    · have hχu : χ u = 1 := by simp [hχ, hu]
      have hLu : L u ≤ t := by
        simp only [hL, ht]
        apply Real.exp_le_exp.mpr
        have : inner ℝ e u ≤ s := hu
        rw [hinner u]
        nlinarith
      rw [hχu]
      nlinarith [h1 u]
    · have hχu : χ u = 0 := by simp [hχ, hu]
      have hLu : t ≤ L u := by
        simp only [hL, ht]
        apply Real.exp_le_exp.mpr
        have : s < inner ℝ e u := lt_of_not_ge hu
        rw [hinner u]
        nlinarith
      rw [hχu]
      nlinarith [h0 u]
  have hmono : ∫ u, (k u - χ u) * t ∂γ ≤ ∫ u, (k u * L u - χ u * L u) ∂γ :=
    integral_mono ((hkint.sub hχint).mul_const t) (hkLint.sub hχLint) hpt
  rw [integral_mul_const, integral_sub hkint hχint, integral_sub hkLint hχLint] at hmono
  have htpos : 0 < t := Real.exp_pos _
  have h1' : 0 ≤ (∫ u, k u ∂γ - ∫ u, χ u ∂γ) * t := by
    apply mul_nonneg _ htpos.le
    rw [hSp]; linarith
  rw [hcmk, ← hSshift, hcmχ]
  linarith

/-- Neyman–Pearson upper bound (half-space `B`), via the lower bound for `1 - k`. -/
theorem c3a_np_up (k : EuclideanSpace ℝ (Fin N) → ℝ) (hk : Measurable k)
    (h0 : ∀ u, 0 ≤ k u) (h1 : ∀ u, k u ≤ 1) (v : EuclideanSpace ℝ (Fin N)) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hB : ∫ u, k u ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) ≤ q) :
    ∫ u, k (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) ≤
      Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q + ‖v‖) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin N)) with hγ
  have hkint := c3a_int_bdd k hk h0 h1
  have hm' : Measurable (fun u => 1 - k u) := measurable_const.sub hk
  have hA : 1 - q ≤ ∫ u, (1 - k u) ∂γ := by
    rw [integral_sub (integrable_const 1) hkint]
    simp; linarith
  have h := c3a_np (fun u => 1 - k u) hm' (fun u => by linarith [h1 u]) (fun u => by linarith [h0 u])
    v (1 - q) (by linarith) (by linarith) hA
  have hkvint : Integrable (fun u => k (u + v)) γ :=
    c3a_int_bdd _ (hk.comp (measurable_id.add_const v)) (fun u => h0 _) (fun u => h1 _)
  rw [integral_sub (integrable_const 1) hkvint, c3a_phiInv_one_sub hq0 hq1,
    show -Cohen2019.Robust.PhiInvReal q - ‖v‖ = -(Cohen2019.Robust.PhiInvReal q + ‖v‖) by ring,
    c3a_phi_neg] at h
  simp at h
  linarith

/-- A null class stays null under a shift (Cameron–Martin). -/
theorem c3a_zero (k : EuclideanSpace ℝ (Fin N) → ℝ) (hk : Measurable k)
    (h0 : ∀ u, 0 ≤ k u) (h1 : ∀ u, k u ≤ 1) (v : EuclideanSpace ℝ (Fin N))
    (hz : ∫ u, k u ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) = 0) :
    ∫ u, k (u + v) ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) = 0 := by
  have hkint := c3a_int_bdd k hk h0 h1
  have hae : k =ᵐ[stdGaussian (EuclideanSpace ℝ (Fin N))] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun u => h0 u) hkint).mp hz
  rw [c3a_cm k v]
  have : (fun u => k u * Real.exp (inner ℝ v u - ‖v‖ ^ 2 / 2)) =ᵐ[stdGaussian _] 0 := by
    filter_upwards [hae] with u hu
    simp [hu]
  rw [integral_congr_ae this]
  simp

end np

/-! ### Main theorem -/

open MeasureTheory ProbabilityTheory Cohen2019.Robust in
theorem solution {d : ℕ} {Y : Type*} (f : EuclideanSpace ℝ (Fin d) → PMF Y)
    (hf : ∀ c : Y, Measurable fun z => f z c) (σ : ℝ) (hσ : 0 < σ)
    (x : EuclideanSpace ℝ (Fin d)) (cA : Y) (pA pB : ℝ)
    (hpA0 : 0 ≤ pA) (hpA1 : pA ≤ 1) (hpB0 : 0 ≤ pB) (hpB1 : pB ≤ 1)
    (hA : pA ≤ classProb f σ x cA) (hAB : pB ≤ pA)
    (hB : ∀ c : Y, c ≠ cA → classProb f σ x c ≤ pB) :
    ∀ δ : EuclideanSpace ℝ (Fin d), ((‖δ‖ : ℝ) : EReal) < certRadius σ pA pB →
      IsSmoothedPrediction f σ (x + δ) cA := by
  classical
  intro δ hR
  unfold IsSmoothedPrediction
  intro c hc
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  set K : Y → EuclideanSpace ℝ (Fin d) → ℝ := fun c u => (f (x + σ • u) c).toReal with hK
  set v : EuclideanSpace ℝ (Fin d) := σ⁻¹ • δ with hv
  have hKm : ∀ c, Measurable (K c) := fun c => (hf c).ennreal_toReal.comp (by fun_prop)
  have hK0 : ∀ c u, 0 ≤ K c u := fun c u => ENNReal.toReal_nonneg
  have hK1 : ∀ c u, K c u ≤ 1 := fun c u =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ _)
  have hKvm : ∀ c, Measurable (fun u => K c (u + v)) :=
    fun c => (hKm c).comp (measurable_id.add_const v)
  have hP : ∀ c, classProb f σ x c = ∫ u, K c u ∂γ := fun c => rfl
  have hPd : ∀ c, classProb f σ (x + δ) c = ∫ u, K c (u + v) ∂γ := by
    intro c
    show ∫ u, (f (x + δ + σ • u) c).toReal ∂γ = _
    congr 1
    funext u
    simp only [hK, hv, smul_add, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
    congr 2
    abel_nf
  have hnv : ‖v‖ = ‖δ‖ / σ := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hσ, div_eq_inv_mul]
  have hone : ∫ _u, (1 : ℝ) ∂γ = 1 := by simp
  have hsum : ∀ c', c' ≠ cA → ∀ u, K c' u + K cA u ≤ 1 := by
    intro c' hc' u
    have h := ENNReal.sum_le_tsum (f := f (x + σ • u)) ({c', cA} : Finset Y)
    rw [Finset.sum_pair hc', PMF.tsum_coe] at h
    have h2 := ENNReal.toReal_mono ENNReal.one_ne_top h
    rwa [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
      ENNReal.toReal_one] at h2
  rw [hPd, hPd]
  rcases eq_or_lt_of_le hpA1 with hA1 | hA1
  · -- `pA = 1`
    rcases eq_or_lt_of_le hpB1 with hB1 | hB1
    · exfalso
      have hT : PhiInv 1 = ⊤ := by simp [PhiInv]
      rw [hA1, hB1, certRadius, hT, EReal.sub_top, EReal.coe_mul_bot_of_pos (by linarith)] at hR
      exact not_lt_bot hR
    · have hint := c3a_int_bdd _ (hKm cA) (hK0 cA) (hK1 cA)
      have hle1 : ∫ u, K cA u ∂γ ≤ 1 :=
        (integral_mono hint (integrable_const 1) (hK1 cA)).trans hone.le
      have hzA : ∫ u, (1 - K cA u) ∂γ = 0 := by
        rw [integral_sub (integrable_const 1) hint, hone]
        rw [hP, hA1] at hA
        linarith
      have hz := c3a_zero (fun u => 1 - K cA u) (measurable_const.sub (hKm cA))
        (fun u => by linarith [hK1 cA u]) (fun u => by linarith [hK0 cA u]) v hzA
      have hintv := c3a_int_bdd _ (hKvm cA) (fun u => hK0 _ _) (fun u => hK1 _ _)
      have hintc := c3a_int_bdd _ (hKvm c) (fun u => hK0 _ _) (fun u => hK1 _ _)
      rw [integral_sub (integrable_const 1) hintv, hone] at hz
      have hs2 : ∫ u, K c (u + v) ∂γ + ∫ u, K cA (u + v) ∂γ ≤ 1 := by
        rw [← integral_add hintc hintv]
        exact (integral_mono (hintc.add hintv) (integrable_const 1)
          (fun u => hsum c hc (u + v))).trans hone.le
      have hc0 : 0 ≤ ∫ u, K c (u + v) ∂γ := integral_nonneg fun u => hK0 _ _
      linarith
  · rcases eq_or_lt_of_le hpB0 with hB0 | hB0
    · -- `pB = 0`
      rcases eq_or_lt_of_le hpA0 with hA0 | hA0
      · exfalso
        have hT : PhiInv 0 = ⊥ := by simp [PhiInv]
        rw [← hA0, ← hB0, certRadius, hT, EReal.bot_sub,
          EReal.coe_mul_bot_of_pos (by linarith)] at hR
        exact not_lt_bot hR
      · have hc0 : ∫ u, K c u ∂γ = 0 :=
          le_antisymm (by rw [← hP]; linarith [hB c hc]) (integral_nonneg (hK0 c))
        rw [c3a_zero (K c) (hKm c) (hK0 c) (hK1 c) v hc0]
        rcases (integral_nonneg (fun u => hK0 cA (u + v)) :
          (0 : ℝ) ≤ ∫ u, K cA (u + v) ∂γ).eq_or_lt with h | h
        · exfalso
          have h2 := c3a_zero (fun u => K cA (u + v)) (hKvm cA) (fun u => hK0 _ _)
            (fun u => hK1 _ _) (-v) h.symm
          simp only [neg_add_cancel_right] at h2
          rw [hP] at hA
          linarith
        · exact h
    · -- interior case `0 < pB ≤ pA < 1`
      have hpA0' : 0 < pA := lt_of_lt_of_le hB0 hAB
      have hpB1' : pB < 1 := lt_of_le_of_lt hAB hA1
      have hreal : ‖δ‖ < σ / 2 * (PhiInvReal pA - PhiInvReal pB) := by
        have e1 : PhiInv pA = ((PhiInvReal pA : ℝ) : EReal) := by
          simp [PhiInv, not_le.mpr hpA0', not_le.mpr hA1]
        have e2 : PhiInv pB = ((PhiInvReal pB : ℝ) : EReal) := by
          simp [PhiInv, not_le.mpr hB0, not_le.mpr hpB1']
        rw [certRadius, e1, e2, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_lt_coe_iff] at hR
        exact hR
      have hup := c3a_np_up (K c) (hKm c) (hK0 c) (hK1 c) v pB hB0 hpB1'
        (by rw [← hP]; exact hB c hc)
      have hlo := c3a_np (K cA) (hKm cA) (hK0 cA) (hK1 cA) v pA hpA0' hA1
        (by rw [← hP]; exact hA)
      have hlt : Phi (PhiInvReal pB + ‖v‖) < Phi (PhiInvReal pA - ‖v‖) := by
        apply c3a_phi_strictMono
        rw [hnv]
        have h2 : ‖δ‖ / σ * 2 < PhiInvReal pA - PhiInvReal pB := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hσ]
          nlinarith
        linarith
      linarith
