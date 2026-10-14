-- Prove2me | solution 1 for BanditGD.Regret.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:08:53.632832+00:00
-- url     : https://prove2.me/submissions/77e2a32d-8812-4b2d-8e38-f8135f6d39c1

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

set_option autoImplicit false

namespace BGDL1

open MeasureTheory Set Metric


theorem polar_integral {d : ℕ} (hd : 1 ≤ d) (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : Integrable G) :
    ∫ w, G w = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      (∫ r in Ioi (0 : ℝ), r ^ (d - 1) * G (r • (u : EuclideanSpace ℝ (Fin d))))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    have : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
      rw [finrank_euclideanSpace_fin]; omega
    exact Module.nontrivial_of_finrank_pos this
  have h1 : ∫ w, G w = ∫ x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set _), G (x : _)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
  have h2 := hmp.integral_comp (Homeomorph.measurableEmbedding _)
    (fun z => G ((z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin d))))
  have hback : ∀ x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set _),
      (((homeomorphUnitSphereProd _ x).2 : ℝ) • ((homeomorphUnitSphereProd _ x).1 :
        EuclideanSpace ℝ (Fin d))) = x := by
    intro x
    have hx : (x : EuclideanSpace ℝ (Fin d)) ≠ 0 := x.2
    simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]
  simp only [hback] at h2
  rw [h1, h2]
  -- integrability on the product
  have hint : Integrable (fun z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0 : ℝ) =>
      G ((z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin d))))
      (((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1))) := by
    have hGc : Integrable (fun x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set _) => G x)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).comap Subtype.val) := by
      have := (integrableOn_iff_comap_subtypeVal
          (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin d))).compl).1
        hG.integrableOn
      simpa [Function.comp_def] using this
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    simpa only [Function.comp_def, hback] using hGc
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  rw [hfr]
  unfold Measure.volumeIoiPow
  simp only [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun a => Real.toNNReal (a ^ (d - 1)) • G (a • (u : EuclideanSpace ℝ (Fin d))))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- the radius function of the shifted ball `closedBall h δ` seen from `0` in direction `u` -/
noncomputable def rho {d : ℕ} (δ : ℝ) (h u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ u h + Real.sqrt (δ ^ 2 - ‖h‖ ^ 2 + inner ℝ u h ^ 2)

theorem mem_ball_iff_le_rho {d : ℕ} {δ : ℝ} {h u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (hh : ‖h‖ < δ) {r : ℝ} (hr : 0 < r) :
    ‖r • u - h‖ ≤ δ ↔ r ≤ rho δ h u := by
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hh
  set a := inner ℝ u h with ha
  set q := δ ^ 2 - ‖h‖ ^ 2 + a ^ 2 with hq
  have hq0 : a ^ 2 < q := by
    have : ‖h‖ ^ 2 < δ ^ 2 := by
      exact pow_lt_pow_left₀ hh (norm_nonneg _) (by norm_num)
    linarith
  have hsq : ‖r • u - h‖ ^ 2 = r ^ 2 - 2 * r * a + ‖h‖ ^ 2 := by
    rw [@norm_sub_sq_real, norm_smul, inner_smul_left, hu, Real.norm_eq_abs, abs_of_pos hr]
    simp [ha]; ring
  have hsqrt_gt : |a| < Real.sqrt q := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hq0
  have hqnn : 0 ≤ q := le_trans (sq_nonneg _) hq0.le
  constructor
  · intro hle
    have h2 : ‖r • u - h‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    have h3 : (r - a) ^ 2 ≤ q := by rw [hsq] at h2; nlinarith
    have h4 : r - a ≤ Real.sqrt q := by
      have := Real.sqrt_le_sqrt h3
      rw [Real.sqrt_sq_eq_abs] at this
      exact le_trans (le_abs_self _) this
    unfold rho; rw [← ha]; linarith
  · intro hle
    unfold rho at hle; rw [← ha] at hle
    have h4 : r - a ≤ Real.sqrt q := by linarith
    have h5 : -(Real.sqrt q) ≤ r - a := by
      have := neg_abs_le a
      have := le_abs_self a
      linarith
    have h3 : (r - a) ^ 2 ≤ q := by
      have := abs_le.2 ⟨h5, h4⟩
      calc (r - a) ^ 2 = |r - a| ^ 2 := (sq_abs _).symm
        _ ≤ Real.sqrt q ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = q := Real.sq_sqrt hqnn
    have h2 : ‖r • u - h‖ ^ 2 ≤ δ ^ 2 := by rw [hsq]; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ.le (by norm_num)).1 h2

noncomputable def rhoD {d : ℕ} (δ : ℝ) (h u : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  innerSL ℝ u + (1 / (2 * Real.sqrt (δ ^ 2 - ‖h‖ ^ 2 + inner ℝ u h ^ 2))) •
    ((2 * inner ℝ u h) • innerSL ℝ u - (2 : ℝ) • innerSL ℝ h)

theorem hasFDerivAt_rho {d : ℕ} {δ : ℝ} {h u : EuclideanSpace ℝ (Fin d)} (hh : ‖h‖ < δ) :
    HasFDerivAt (fun k => rho δ k u) (rhoD δ h u) h := by
  have h1 : HasFDerivAt (fun k : EuclideanSpace ℝ (Fin d) => inner ℝ u k) (innerSL ℝ u) h :=
    (innerSL ℝ u).hasFDerivAt
  have h2 : HasFDerivAt (fun k : EuclideanSpace ℝ (Fin d) => δ ^ 2 - ‖k‖ ^ 2 + inner ℝ u k ^ 2)
      ((2 * inner ℝ u h) • innerSL ℝ u - (2 : ℝ) • innerSL ℝ h) h := by
    have a := (hasFDerivAt_id h).norm_sq
    have b := h1.pow 2
    refine (((hasFDerivAt_const (δ ^ 2) h).sub a).add b).congr_fderiv ?_
    ext v
    simp; ring
  have hq : δ ^ 2 - ‖h‖ ^ 2 + inner ℝ u h ^ 2 ≠ 0 := by
    have : ‖h‖ ^ 2 < δ ^ 2 := pow_lt_pow_left₀ hh (norm_nonneg _) (by norm_num)
    have := sq_nonneg (inner ℝ u h)
    exact ne_of_gt (by linarith)
  exact h1.add (h2.sqrt hq)

theorem norm_rhoD_le {d : ℕ} {δ : ℝ} {h u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (hδ : 0 < δ) (hh : ‖h‖ ≤ δ / 2) : ‖rhoD δ h u‖ ≤ 3 := by
  set a := inner ℝ u h with ha
  have hab : |a| ≤ ‖h‖ := by
    have := abs_real_inner_le_norm u h
    rw [hu, one_mul] at this
    exact this
  set q := δ ^ 2 - ‖h‖ ^ 2 + a ^ 2 with hq
  have hq1 : (δ / 2) ^ 2 ≤ q := by
    have : ‖h‖ ^ 2 ≤ (δ / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith [sq_nonneg a]
  have hsq : δ / 2 ≤ Real.sqrt q := Real.le_sqrt_of_sq_le hq1
  have hX : ‖(2 * a) • innerSL ℝ u - (2 : ℝ) • innerSL ℝ h‖ ≤ 4 * ‖h‖ := by
    calc _ ≤ ‖(2 * a) • innerSL ℝ u‖ + ‖(2 : ℝ) • innerSL ℝ h‖ := norm_sub_le _ _
      _ = |2 * a| * 1 + 2 * ‖h‖ := by
          rw [norm_smul, norm_smul, innerSL_apply_norm, innerSL_apply_norm, hu,
            Real.norm_eq_abs, Real.norm_eq_abs]
          norm_num
      _ ≤ 4 * ‖h‖ := by rw [abs_mul]; norm_num; linarith
  have hc : ‖1 / (2 * Real.sqrt q)‖ ≤ 1 / δ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le hδ (by linarith)
  unfold rhoD
  rw [← ha, ← hq]
  calc _ ≤ ‖innerSL ℝ u‖ + ‖(1 / (2 * Real.sqrt q)) •
        ((2 * a) • innerSL ℝ u - (2 : ℝ) • innerSL ℝ h)‖ := norm_add_le _ _
    _ ≤ 1 + (1 / δ) * (4 * ‖h‖) := by
        rw [innerSL_apply_norm, hu, norm_smul]
        linarith [mul_le_mul hc hX (norm_nonneg _) (by positivity : (0:ℝ) ≤ 1 / δ)]
    _ ≤ 3 := by
        have : (1 / δ) * (4 * ‖h‖) ≤ 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hδ]; linarith
        linarith

theorem rho_pos {d : ℕ} {δ : ℝ} {h u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (hh : ‖h‖ < δ) : 0 < rho δ h u := by
  set a := inner ℝ u h with ha
  have hab : |a| ≤ ‖h‖ := by
    have := abs_real_inner_le_norm u h
    rw [hu, one_mul] at this
    exact this
  have hq0 : a ^ 2 < δ ^ 2 - ‖h‖ ^ 2 + a ^ 2 := by
    have : ‖h‖ ^ 2 < δ ^ 2 := pow_lt_pow_left₀ hh (norm_nonneg _) (by norm_num)
    linarith
  have : |a| < Real.sqrt (δ ^ 2 - ‖h‖ ^ 2 + a ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hq0
  unfold rho; rw [← ha]
  linarith [neg_abs_le a]

theorem rho_le {d : ℕ} {δ : ℝ} {h u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (hδ : 0 < δ) : rho δ h u ≤ δ + 2 * ‖h‖ := by
  set a := inner ℝ u h with ha
  have hab : |a| ≤ ‖h‖ := by
    have := abs_real_inner_le_norm u h
    rw [hu, one_mul] at this
    exact this
  have : Real.sqrt (δ ^ 2 - ‖h‖ ^ 2 + a ^ 2) ≤ δ + |a| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg a, sq_abs a, sq_nonneg ‖h‖]
  unfold rho; rw [← ha]
  linarith [le_abs_self a]

theorem rho_zero {d : ℕ} {δ : ℝ} (u : EuclideanSpace ℝ (Fin d)) (hδ : 0 < δ) :
    rho δ 0 u = δ := by
  simp [rho, Real.sqrt_sq hδ.le]

theorem rhoD_zero {d : ℕ} (δ : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    rhoD δ 0 u = innerSL ℝ u := by
  simp [rhoD]


noncomputable def phi {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (x u : EuclideanSpace ℝ (Fin d))
    (r : ℝ) : ℝ :=
  r ^ (d - 1) * g (x + r • u)

theorem ball_polar {d : ℕ} (hd : 1 ≤ d) {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    (x h : EuclideanSpace ℝ (Fin d)) {δ : ℝ} (hh : ‖h‖ < δ) :
    ∫ w, (closedBall h δ).indicator (fun w => g (x + w)) w =
      ∫ u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (∫ r in (0 : ℝ)..rho δ h (u : EuclideanSpace ℝ (Fin d)), phi g x u r)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) := by
  have hint : Integrable ((closedBall h δ).indicator (fun w => g (x + w))) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (hg.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      (isCompact_closedBall h δ)
  rw [polar_integral hd _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hu : ‖(u : EuclideanSpace ℝ (Fin d))‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
  have hρ := rho_pos hu hh
  have key : ∀ r ∈ Ioi (0 : ℝ), r ^ (d - 1) * (closedBall h δ).indicator (fun w => g (x + w))
      (r • (u : EuclideanSpace ℝ (Fin d))) = (Iic (rho δ h u)).indicator (phi g x u) r := by
    intro r hr
    by_cases hle : r ≤ rho δ h u
    · have hm : r • (u : EuclideanSpace ℝ (Fin d)) ∈ closedBall h δ := by
        rw [mem_closedBall, dist_eq_norm]; exact (mem_ball_iff_le_rho hu hh hr).2 hle
      rw [indicator_of_mem hm, indicator_of_mem (show r ∈ Iic (rho δ h u) from hle)]
      rfl
    · have hm : r • (u : EuclideanSpace ℝ (Fin d)) ∉ closedBall h δ := by
        rw [mem_closedBall, dist_eq_norm]
        exact fun h' => hle ((mem_ball_iff_le_rho hu hh hr).1 h')
      rw [indicator_of_notMem hm, indicator_of_notMem (show r ∉ Iic (rho δ h u) from hle)]
      simp
  dsimp only
  rw [setIntegral_congr_fun measurableSet_Ioi key, setIntegral_indicator measurableSet_Iic,
    Ioi_inter_Iic, intervalIntegral.integral_of_le hρ.le]

theorem hasFDerivAt_ballIntegral {d : ℕ} (hd : 1 ≤ d) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Continuous g) (x : EuclideanSpace ℝ (Fin d)) {δ : ℝ} (hδ : 0 < δ) :
    HasFDerivAt (fun h => ∫ w, (closedBall h δ).indicator (fun w => g (x + w)) w)
      (∫ u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (δ ^ (d - 1) * g (x + δ • (u : EuclideanSpace ℝ (Fin d)))) •
          innerSL ℝ (u : EuclideanSpace ℝ (Fin d))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)) 0 := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (2 * δ)).exists_bound_of_continuousOn hg.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x (mem_closedBall_self (by positivity)))
  have hphic : ∀ u : EuclideanSpace ℝ (Fin d), Continuous (phi g x u) := by
    intro u; unfold phi; fun_prop
  have hphib : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ r, 0 ≤ r → r ≤ 2 * δ →
      ‖phi g x u r‖ ≤ (2 * δ) ^ (d - 1) * M := by
    intro u hu r hr0 hr
    unfold phi
    rw [norm_mul]
    have h1 : ‖r ^ (d - 1)‖ ≤ (2 * δ) ^ (d - 1) := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact pow_le_pow_left₀ hr0 hr _
    have h2 : ‖g (x + r • u)‖ ≤ M := by
      apply hM
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hrhoc : ∀ h : EuclideanSpace ℝ (Fin d),
      Continuous fun u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        rho δ h (u : EuclideanSpace ℝ (Fin d)) := by
    intro h; unfold rho; fun_prop
  have hFc : ∀ h : EuclideanSpace ℝ (Fin d),
      Continuous fun u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        ∫ r in (0 : ℝ)..rho δ h (u : EuclideanSpace ℝ (Fin d)), phi g x u r := by
    intro h
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) r => phi g x u r)
    · unfold phi; fun_prop
    · exact hrhoc h
  have hF'0 : (fun u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      phi g x u (rho δ 0 (u : EuclideanSpace ℝ (Fin d))) • rhoD δ 0 (u : EuclideanSpace ℝ (Fin d)))
      = fun u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          (δ ^ (d - 1) * g (x + δ • (u : EuclideanSpace ℝ (Fin d)))) •
          innerSL ℝ (u : EuclideanSpace ℝ (Fin d)) := by
    funext u
    rw [rho_zero _ hδ, rhoD_zero]
    rfl
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)
    (F := fun h (u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
      ∫ r in (0 : ℝ)..rho δ h (u : EuclideanSpace ℝ (Fin d)), phi g x u r)
    (F' := fun h (u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
      phi g x u (rho δ h (u : EuclideanSpace ℝ (Fin d))) • rhoD δ h (u : EuclideanSpace ℝ (Fin d)))
    (x₀ := 0) (s := ball 0 (δ / 2)) (bound := fun _ => (2 * δ) ^ (d - 1) * M * 3)
    (ball_mem_nhds _ (by positivity))
    (Filter.Eventually.of_forall fun h => (hFc h).aestronglyMeasurable)
    ((hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (by
      rw [hF'0]
      apply Continuous.aestronglyMeasurable
      fun_prop)
    (Filter.Eventually.of_forall fun u h hh => by
      have hu : ‖(u : EuclideanSpace ℝ (Fin d))‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
      rw [mem_ball_zero_iff] at hh
      have hρ0 := rho_pos (δ := δ) (h := h) hu (by linarith)
      have hρ1 := rho_le (h := h) hu hδ
      rw [norm_smul]
      exact mul_le_mul (hphib _ hu _ hρ0.le (by linarith)) (norm_rhoD_le hu hδ hh.le)
        (norm_nonneg _) (by positivity))
    (integrable_const _)
    (Filter.Eventually.of_forall fun u h hh => by
      rw [mem_ball_zero_iff] at hh
      exact ((hphic u).integral_hasStrictDerivAt 0 _).hasDerivAt.comp_hasFDerivAt h
        (hasFDerivAt_rho (by linarith)))
  rw [hF'0] at key
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) hδ] with h hh
  rw [mem_ball_zero_iff] at hh
  exact ball_polar hd hg x h hh


theorem smoothedLoss_eq {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (z : EuclideanSpace ℝ (Fin d)) :
    RegretBandits.Nonlinear.smoothedLoss d δ g z =
      ((volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)⁻¹ * (δ ^ d)⁻¹ *
        ∫ w, (closedBall (0 : EuclideanSpace ℝ (Fin d)) δ).indicator (fun w => g (z + w)) w := by
  unfold RegretBandits.Nonlinear.smoothedLoss RegretBandits.Nonlinear.uniformBall
  rw [integral_smul_measure, ← integral_indicator measurableSet_closedBall]
  have hcv : (fun b => (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator
      (fun b => g (z + δ • b)) b) = fun b => (closedBall (0 : EuclideanSpace ℝ (Fin d)) δ).indicator
        (fun w => g (z + w)) (δ • b) := by
    funext b
    have hiff : δ • b ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) δ ↔
        b ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos hδ]
      constructor
      · intro h; nlinarith [norm_nonneg b]
      · intro h; nlinarith [norm_nonneg b]
    by_cases hb : b ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
    · rw [indicator_of_mem hb, indicator_of_mem (hiff.2 hb)]
    · rw [indicator_of_notMem hb, indicator_of_notMem (fun h => hb (hiff.1 h))]
  rw [hcv, Measure.integral_comp_smul]
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  rw [hfr, ENNReal.toReal_inv, smul_eq_mul, smul_eq_mul, abs_of_pos (by positivity)]
  ring

theorem ballIntegral_translate {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (δ : ℝ)
    (x h : EuclideanSpace ℝ (Fin d)) :
    ∫ w, (closedBall (0 : EuclideanSpace ℝ (Fin d)) δ).indicator (fun w => g (x + h + w)) w =
      ∫ w, (closedBall h δ).indicator (fun w => g (x + w)) w := by
  rw [← integral_add_right_eq_self (μ := volume)
    (fun w => (closedBall h δ).indicator (fun w => g (x + w)) w) h]
  congr 1
  funext w
  have hiff : w + h ∈ closedBall h δ ↔ w ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) δ := by
    rw [mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm, add_sub_cancel_right, sub_zero]
  by_cases hw : w ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) δ
  · rw [indicator_of_mem hw, indicator_of_mem (hiff.2 hw)]
    congr 1; abel
  · rw [indicator_of_notMem hw, indicator_of_notMem (fun h' => hw (hiff.1 h'))]

theorem lemma1_cont {d : ℕ} (hd : 1 ≤ d) {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (RegretBandits.Nonlinear.smoothedLoss d δ g)
      (((d : ℝ) / δ) • ∫ v, g (x + δ • v) • v ∂(RegretBandits.Nonlinear.uniformSphere d)) x := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    have : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
      rw [finrank_euclideanSpace_fin]; omega
    exact Module.nontrivial_of_finrank_pos this
  set V : ℝ := (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hV
  set c0 : ℝ := V⁻¹ * (δ ^ d)⁻¹ with hc0
  set K : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun h => ∫ w, (closedBall h δ).indicator (fun w => g (x + w)) w with hK
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere with hσ
  set L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := ∫ u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (δ ^ (d - 1) * g (x + δ • (u : EuclideanSpace ℝ (Fin d)))) •
          innerSL ℝ (u : EuclideanSpace ℝ (Fin d)) ∂σ with hL
  have hKd : HasFDerivAt K L 0 := hasFDerivAt_ballIntegral hd hg x hδ
  have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => z - x)
      (ContinuousLinearMap.id ℝ _) x := (hasFDerivAt_id x).sub_const x
  have h3 : HasFDerivAt K L ((fun z : EuclideanSpace ℝ (Fin d) => z - x) x) := by
    rw [show (fun z : EuclideanSpace ℝ (Fin d) => z - x) x = 0 from sub_self x]; exact hKd
  have h4 := (HasFDerivAt.comp (g := K) (f := fun z : EuclideanSpace ℝ (Fin d) => z - x) x h3 h2).const_mul c0
  have hS : ∀ z, RegretBandits.Nonlinear.smoothedLoss d δ g z = c0 * (K ∘ fun z => z - x) z := by
    intro z
    rw [smoothedLoss_eq hδ, Function.comp_apply, hK]
    dsimp only
    rw [← ballIntegral_translate g δ x (z - x), show x + (z - x) = z by abel]
  have h5 : HasFDerivAt (RegretBandits.Nonlinear.smoothedLoss d δ g)
      (c0 • (L.comp (ContinuousLinearMap.id ℝ _))) x :=
    h4.congr_of_eventuallyEq (Filter.Eventually.of_forall hS)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h5.congr_fderiv ?_
  -- identify the derivative
  have hint : Integrable (fun u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      (δ ^ (d - 1) * g (x + δ • (u : EuclideanSpace ℝ (Fin d)))) •
          innerSL ℝ (u : EuclideanSpace ℝ (Fin d))) σ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hint2 : Integrable (fun u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      g (x + δ • (u : EuclideanSpace ℝ (Fin d))) • (u : EuclideanSpace ℝ (Fin d))) σ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hunif : ∫ v, g (x + δ • v) • v ∂(RegretBandits.Nonlinear.uniformSphere d) =
      ((d : ℝ) * V)⁻¹ • ∫ u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        g (x + δ • (u : EuclideanSpace ℝ (Fin d))) • (u : EuclideanSpace ℝ (Fin d)) ∂σ := by
    unfold RegretBandits.Nonlinear.uniformSphere RegretBandits.Nonlinear.sphereMeasure
    rw [integral_smul_measure,
      (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).integral_map]
    congr 1
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ,
      Measure.toSphere_apply_univ, ENNReal.toReal_inv, ENNReal.toReal_mul, hV,
      Measure.addHaar_closedBall_eq_addHaar_ball, finrank_euclideanSpace_fin]
    simp
  ext v
  rw [hunif]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  rw [hL, ContinuousLinearMap.integral_apply hint, real_inner_comm, real_inner_smul_right,
    real_inner_smul_right, ← integral_inner hint2]
  have e1 : ∀ u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ((δ ^ (d - 1) * g (x + δ • (u : EuclideanSpace ℝ (Fin d)))) •
        innerSL ℝ (u : EuclideanSpace ℝ (Fin d))) v =
      δ ^ (d - 1) * (g (x + δ • (u : EuclideanSpace ℝ (Fin d))) *
        inner ℝ (u : EuclideanSpace ℝ (Fin d)) v) := by
    intro u; simp [mul_assoc]
  have e2 : ∀ u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ v (g (x + δ • (u : EuclideanSpace ℝ (Fin d))) • (u : EuclideanSpace ℝ (Fin d))) =
      g (x + δ • (u : EuclideanSpace ℝ (Fin d))) * inner ℝ (u : EuclideanSpace ℝ (Fin d)) v := by
    intro u; rw [real_inner_smul_right, real_inner_comm]
  simp_rw [e1, e2]
  rw [integral_const_mul]
  have hVpos : 0 < V := by
    rw [hV, Measure.addHaar_closedBall_eq_addHaar_ball]
    exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel, hc0]
  field_simp
  ring

theorem lemma1_gen {d : ℕ} (hd : 1 ≤ d) (f : EuclideanSpace ℝ (Fin d) → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin d)) (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U)
    (hxU : Metric.closedBall x δ ⊆ U) (hf : ContinuousOn f U) :
    HasGradientAt (RegretBandits.Nonlinear.smoothedLoss d δ f)
      (((d : ℝ) / δ) • ∫ v, f (x + δ • v) • v ∂(RegretBandits.Nonlinear.uniformSphere d)) x := by
  obtain ⟨ε, hε, hεU⟩ := (isCompact_closedBall x δ).exists_cthickening_subset_open hU hxU
  rw [cthickening_closedBall hε.le hδ.le] at hεU
  set s := closedBall x (ε + δ) with hs
  let F : C(s, ℝ) := ⟨s.restrict f, (hf.mono hεU).restrict⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq isClosed_closedBall F
  have hGf : ∀ y ∈ s, G y = f y := by
    intro y hy
    exact congrArg (fun φ : C(s, ℝ) => φ ⟨y, hy⟩) hG
  have hmem : ∀ z ∈ ball x ε, ∀ b ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      z + δ • b ∈ s := by
    intro z hz b hb
    rw [hs, mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall_zero_iff] at hb
    calc ‖z + δ • b - x‖ ≤ ‖z - x‖ + ‖δ • b‖ := by
          rw [show z + δ • b - x = (z - x) + δ • b by abel]; exact norm_add_le _ _
      _ ≤ ε + δ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
          nlinarith [norm_nonneg b]
  have heq : RegretBandits.Nonlinear.smoothedLoss d δ G =ᶠ[nhds x]
      RegretBandits.Nonlinear.smoothedLoss d δ f := by
    filter_upwards [ball_mem_nhds x hε] with z hz
    unfold RegretBandits.Nonlinear.smoothedLoss RegretBandits.Nonlinear.uniformBall
    rw [integral_smul_measure, integral_smul_measure]
    congr 1
    exact setIntegral_congr_fun measurableSet_closedBall fun b hb => hGf _ (hmem z hz b hb)
  have hgrad : ∫ v, G (x + δ • v) • v ∂(RegretBandits.Nonlinear.uniformSphere d) =
      ∫ v, f (x + δ • v) • v ∂(RegretBandits.Nonlinear.uniformSphere d) := by
    unfold RegretBandits.Nonlinear.uniformSphere RegretBandits.Nonlinear.sphereMeasure
    rw [integral_smul_measure, integral_smul_measure,
      (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).integral_map,
      (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).integral_map]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hu : (u : EuclideanSpace ℝ (Fin d)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm.1 u.2]
    dsimp only
    rw [hGf _ (hmem x (mem_ball_self hε) _ hu)]
  have key := lemma1_cont hd G.continuous hδ x
  rw [hgrad] at key
  rw [hasGradientAt_iff_hasFDerivAt] at key ⊢
  exact key.congr_of_eventuallyEq heq.symm

end BGDL1

open MeasureTheory in
theorem solution {d : ℕ} (hd : 1 ≤ d) (f : EuclideanSpace ℝ (Fin d) → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin d)) (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U)
    (hxU : Metric.closedBall x δ ⊆ U) (hf : ContinuousOn f U) :
    HasGradientAt (RegretBandits.Nonlinear.smoothedLoss d δ f)
      (((d : ℝ) / δ) • ∫ v, f (x + δ • v) • v ∂(RegretBandits.Nonlinear.uniformSphere d)) x := by
  exact BGDL1.lemma1_gen hd f δ hδ x U hU hxU hf
