-- Prove2me | solution 1 for BanditGD.Regret.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:36:26.219712+00:00
-- url     : https://prove2.me/submissions/c850eed6-0f5a-434a-936b-8a3a5344fdf6

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD
import Definitions.Def_BanditGD_Regret_Setting

/-! 9918f561 BanditGD.Regret.eq_10 (Flaxman-Kalai-McMahan display (10)).
BGDL1: lemma 1 (gradient of the ball-smoothed loss) via polar coordinates, no divergence theorem.
BGDL2: smoothed regret bound (projection lemmas, deterministic run Yf, independence, OGD telescoping).
obs1/obs3: the proved observations 1 and 3 (copied from our accepted proofs 86d7dab5, 96e24d05).
BGDL3: assembly. No Theorems import. -/

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



set_option autoImplicit false

namespace BGDL2

open MeasureTheory Set Metric RegretBandits.Nonlinear

theorem nearest_inner {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    {p y : EuclideanSpace ℝ (Fin d)} (hy : IsNearestPoint K p y) :
    ∀ w ∈ K, inner ℝ (p - y) (w - y) ≤ 0 := by
  haveI : Nonempty K := ⟨⟨y, hy.1⟩⟩
  have hbdd : BddBelow (Set.range fun w : K => ‖p - (w : EuclideanSpace ℝ (Fin d))‖) :=
    ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
  have hinf : ‖p - y‖ = ⨅ w : K, ‖p - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      have := hy.2 w w.2
      rwa [norm_sub_rev y p, norm_sub_rev (w : EuclideanSpace ℝ (Fin d)) p] at this
    · exact ciInf_le hbdd ⟨y, hy.1⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hK hy.1).1 hinf

theorem nearest_nonexp {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    {p y z : EuclideanSpace ℝ (Fin d)} (hy : IsNearestPoint K p y) (hz : z ∈ K) :
    ‖y - z‖ ^ 2 ≤ ‖p - z‖ ^ 2 := by
  have h := nearest_inner hK hy z hz
  have e : p - z = (p - y) + (y - z) := by abel
  rw [e, @norm_add_sq_real]
  have : inner ℝ (p - y) (y - z) = - inner ℝ (p - y) (z - y) := by
    rw [← inner_neg_right, neg_sub]
  nlinarith [sq_nonneg ‖p - y‖]

theorem nearest_firm {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    {p q y y' : EuclideanSpace ℝ (Fin d)} (hy : IsNearestPoint K p y)
    (hy' : IsNearestPoint K q y') : ‖y - y'‖ ≤ ‖p - q‖ := by
  have h1 := nearest_inner hK hy y' hy'.1
  have h2 := nearest_inner hK hy' y hy.1
  have key : ‖y - y'‖ ^ 2 ≤ inner ℝ (p - q) (y - y') := by
    have e1 : inner ℝ (p - q) (y - y') = inner ℝ (p - y) (y - y') + inner ℝ (q - y') (y' - y)
        + ‖y - y'‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      have : p - q = (p - y) - (q - y') + (y - y') := by abel
      rw [this, inner_add_left, inner_sub_left]
      have : inner ℝ (q - y') (y - y') = - inner ℝ (q - y') (y' - y) := by
        rw [← inner_neg_right, neg_sub]
      rw [this]; ring
    have h1' : inner ℝ (p - y) (y - y') = - inner ℝ (p - y) (y' - y) := by
      rw [← inner_neg_right, neg_sub]
    have h2' : inner ℝ (q - y') (y' - y) = - inner ℝ (q - y') (y - y') := by
      rw [← inner_neg_right, neg_sub]
    rw [e1, h1', h2']
    linarith
  have hc := real_inner_le_norm (p - q) (y - y')
  by_cases h0 : ‖y - y'‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖y - y'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem nearest_unique {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    {p y y' : EuclideanSpace ℝ (Fin d)} (hy : IsNearestPoint K p y)
    (hy' : IsNearestPoint K p y') : y = y' := by
  have := nearest_firm hK hy hy'
  rw [sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem exists_nearest {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    (hKc : IsClosed K) (hne : K.Nonempty) (p : EuclideanSpace ℝ (Fin d)) :
    ∃ y, IsNearestPoint K p y := by
  obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hKc.isComplete hK p
  refine ⟨v, hv, fun w hw => ?_⟩
  have hbdd : BddBelow (Set.range fun w : K => ‖p - (w : EuclideanSpace ℝ (Fin d))‖) :=
    ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
  rw [norm_sub_rev v p, norm_sub_rev w p, hmin]
  exact ciInf_le hbdd ⟨w, hw⟩

open Classical in
noncomputable def proj {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if h : ∃ y, IsNearestPoint K p y then h.choose else 0

theorem proj_spec {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    (hKc : IsClosed K) (hne : K.Nonempty) (p : EuclideanSpace ℝ (Fin d)) :
    IsNearestPoint K p (proj K p) := by
  have h := exists_nearest hK hKc hne p
  unfold proj
  rw [dif_pos h]
  exact h.choose_spec

theorem proj_eq {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    (hKc : IsClosed K) (hne : K.Nonempty) {p y : EuclideanSpace ℝ (Fin d)}
    (hy : IsNearestPoint K p y) : proj K p = y :=
  nearest_unique hK (proj_spec hK hKc hne p) hy

theorem proj_continuous {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    (hKc : IsClosed K) (hne : K.Nonempty) : Continuous (proj K) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  exact nearest_firm hK (proj_spec hK hKc hne p) (proj_spec hK hKc hne q)


open scoped Pointwise

theorem indep_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X U : Ω → EuclideanSpace ℝ (Fin d)} (hX : Measurable X)
    (hU : Measurable U) (hXU : ProbabilityTheory.IndepFun X U P)
    (F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) (hF : Measurable F) (M : ℝ)
    (hFM : ∀ p, |F p| ≤ M) :
    ∫ ω, F (X ω, U ω) ∂P = ∫ ω, (∫ v, F (X ω, v) ∂(P.map U)) ∂P := by
  have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable
    hU.aemeasurable).1 hXU
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  have hint : Integrable F ((P.map X).prod (P.map U)) :=
    (integrable_const M).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hFM p)
  calc ∫ ω, F (X ω, U ω) ∂P = ∫ p, F p ∂(P.map (fun ω => (X ω, U ω))) :=
        (integral_map (hX.prodMk hU).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂((P.map X).prod (P.map U)) := by rw [hmap]
    _ = ∫ k, ∫ v, F (k, v) ∂(P.map U) ∂(P.map X) := integral_prod F hint
    _ = ∫ ω, (∫ v, F (X ω, v) ∂(P.map U)) ∂P :=
        integral_map hX.aemeasurable hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

theorem ball_sub {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hrS : Metric.closedBall 0 r ⊆ S) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ x ∈ (1 - α) • S, Metric.closedBall x (α * r) ⊆ S := by
  intro x hx y hy
  obtain ⟨s, hs, rfl⟩ := hx
  dsimp only at hy ⊢
  rcases hα0.eq_or_lt with h0 | hpos
  · subst h0
    rw [zero_mul, Metric.closedBall_zero, Set.mem_singleton_iff] at hy
    rw [hy]
    simpa using hs
  · have hz : α⁻¹ • (y - (1 - α) • s) ∈ S := by
      apply hrS
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hpos]
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      rw [inv_mul_le_iff₀ hpos]
      exact hy
    have key : y = (1 - α) • s + α • (α⁻¹ • (y - (1 - α) • s)) := by
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      abel
    rw [key]
    exact hSconv hs hz (by linarith) hα0 (by ring)

theorem Kp_sub_ball {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ)
    (hSR : S ⊆ Metric.closedBall 0 R) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (1 - α) • S ⊆ Metric.closedBall 0 R := by
  rintro _ ⟨s, hs, rfl⟩
  have h := hSR hs
  rw [mem_closedBall_zero_iff] at h ⊢
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  nlinarith [norm_nonneg s]

noncomputable def Yf {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (ct : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ν δ : ℝ) :
    ℕ → (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)
  | 0, _ => 0
  | 1, _ => 0
  | (t + 2), w => proj K (Yf K ct ν δ (t + 1) w -
      (ν * ct (t + 1) (Yf K ct ν δ (t + 1) w + δ • w (t + 1))) • w (t + 1))

theorem Yf_succ {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (ct : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ν δ : ℝ) (w : ℕ → EuclideanSpace ℝ (Fin d))
    {t : ℕ} (ht : 1 ≤ t) :
    Yf K ct ν δ (t + 1) w = proj K (Yf K ct ν δ t w - (ν * ct t (Yf K ct ν δ t w + δ • w t)) • w t) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rfl

theorem Yf_mem {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    (hKc : IsClosed K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K)
    (ct : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ν δ : ℝ) (w : ℕ → EuclideanSpace ℝ (Fin d)) :
    ∀ t, Yf K ct ν δ t w ∈ K
  | 0 => h0
  | 1 => h0
  | (t + 2) => (proj_spec hK hKc ⟨0, h0⟩ _).1

theorem Yf_measurable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    (hKc : IsClosed K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K)
    (ct : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hct : ∀ t, Measurable (ct t)) (ν δ : ℝ) :
    ∀ t, Measurable (Yf K ct ν δ t)
  | 0 => measurable_const
  | 1 => measurable_const
  | (t + 2) => by
      have ih := Yf_measurable hK hKc h0 ct hct ν δ (t + 1)
      have hw : Measurable fun w : ℕ → EuclideanSpace ℝ (Fin d) => w (t + 1) :=
        measurable_pi_apply (t + 1)
      exact (proj_continuous hK hKc ⟨0, h0⟩).measurable.comp
        (ih.sub ((measurable_const.mul ((hct _).comp (ih.add (hw.const_smul δ)))).smul hw))

theorem Yf_local {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (ct : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ν δ : ℝ) :
    ∀ t (w w' : ℕ → EuclideanSpace ℝ (Fin d)), (∀ s < t, w s = w' s) →
      Yf K ct ν δ t w = Yf K ct ν δ t w'
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | (t + 2), w, w', h => by
      have ih := Yf_local K ct ν δ (t + 1) w w' (fun s hs => h s (by omega))
      have hw : w (t + 1) = w' (t + 1) := h (t + 1) (by omega)
      show proj K (Yf K ct ν δ (t + 1) w -
          (ν * ct (t + 1) (Yf K ct ν δ (t + 1) w + δ • w (t + 1))) • w (t + 1)) =
        proj K (Yf K ct ν δ (t + 1) w' -
          (ν * ct (t + 1) (Yf K ct ν δ (t + 1) w' + δ • w' (t + 1))) • w' (t + 1))
      rw [ih, hw]

open Classical in
theorem run_eq_Yf {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} (hSconv : Convex ℝ S)
    (hSclosed : IsClosed S) {r : ℝ} (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S)
    {α δ ν : ℝ} (hδ : 0 < δ) (hδα : δ < α * r) (hα1 : α ≤ 1)
    (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (u y : ℕ → EuclideanSpace ℝ (Fin d))
    (hu : ∀ t, ‖u t‖ = 1) (hrun : BanditGD.Regret.IsBGDRun S α δ ν c u y) :
    ∀ t, 1 ≤ t → y t = Yf ((1 - α) • S)
      (fun t x => if x ∈ interior S then c t x else 0) ν δ t u := by
  have hα0 : 0 < α := by
    by_contra h; push_neg at h; nlinarith
  have h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S := hrS (Metric.mem_closedBall_self hr.le)
  have hK : Convex ℝ ((1 - α) • S) := hSconv.smul _
  have hKc : IsClosed ((1 - α) • S) := hSclosed.smul₀ _
  have h0K : (0 : EuclideanSpace ℝ (Fin d)) ∈ (1 - α) • S := ⟨0, h0S, smul_zero _⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hrun.1
  | succ t ht ih =>
    rw [Yf_succ _ _ _ _ _ ht, ← ih]
    have hmem : y t + δ • u t ∈ interior S := by
      have hyK : y t ∈ (1 - α) • S := by rw [ih]; exact Yf_mem hK hKc h0K _ _ _ _ _
      apply interior_maximal (Metric.ball_subset_closedBall.trans
        (ball_sub S hSconv r hrS α hα0.le hα1 _ hyK)) Metric.isOpen_ball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
        Real.norm_eq_abs, abs_of_pos hδ]
      exact hδα
    simp only [if_pos hmem]
    exact (proj_eq hK hKc ⟨0, h0K⟩ (hrun.2 t ht)).symm


theorem grad_ineq {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hf : ConvexOn ℝ K f) {k z g : EuclideanSpace ℝ (Fin d)} (hk : k ∈ K) (hz : z ∈ K)
    (hg : HasGradientAt f g k) : inner ℝ g (z - k) ≤ f z - f k := by
  set φ : ℝ → ℝ := fun t => f (k + t • (z - k)) with hφ
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, k + t • (z - k) ∈ K := by
    intro t ht
    have : k + t • (z - k) = (1 - t) • k + t • z := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact hf.1 hk hz (by linarith [ht.2]) ht.1 (by ring)
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) φ := by
    refine ⟨convex_Icc 0 1, fun a ha b hb p q hp hq hpq => ?_⟩
    have e : k + (p • a + q • b) • (z - k) = p • (k + a • (z - k)) + q • (k + b • (z - k)) := by
      have hk' : p • k + q • k = k := by rw [← add_smul, hpq, one_smul]
      calc k + (p • a + q • b) • (z - k)
          = (p • k + q • k) + ((p * a) • (z - k) + (q * b) • (z - k)) := by
            rw [hk', add_smul, smul_eq_mul, smul_eq_mul]
        _ = p • (k + a • (z - k)) + q • (k + b • (z - k)) := by
            rw [smul_add, smul_add, smul_smul, smul_smul]; abel
    simp only [hφ, smul_eq_mul]
    rw [show k + (p * a + q * b) • (z - k) = k + (p • a + q • b) • (z - k) by simp [smul_eq_mul], e]
    exact hf.2 (hseg a ha) (hseg b hb) hp hq hpq
  have hline : HasDerivAt (fun t : ℝ => k + t • (z - k)) (z - k) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (z - k)).const_add k
  have hderiv : HasDerivAt φ (inner ℝ g (z - k)) 0 := by
    have := (hasGradientAt_iff_hasFDerivAt.1 hg).comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    simpa [Function.comp_def] using this
  have h := hconv.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one
    hderiv.hasDerivWithinAt
  simpa [slope, hφ] using h

theorem uniformBall_prob {d : ℕ} (hd : 1 ≤ d) : IsProbabilityMeasure (uniformBall d) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    have : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
      rw [finrank_euclideanSpace_fin]; omega
    exact Module.nontrivial_of_finrank_pos this
  constructor
  unfold uniformBall
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  have h0 : volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 := by
    rw [Measure.addHaar_closedBall_eq_addHaar_ball]
    exact (measure_ball_pos _ _ one_pos).ne'
  have htop : volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  exact ENNReal.inv_mul_cancel h0 htop

theorem uniformBall_ae {d : ℕ} : ∀ᵐ b ∂(uniformBall d), b ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  unfold uniformBall
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_closedBall) _

theorem smooth_integrable {d : ℕ} (hd : 1 ≤ d) {f : EuclideanSpace ℝ (Fin d) → ℝ} {k : EuclideanSpace ℝ (Fin d)}
    {δ : ℝ} (hδ : 0 ≤ δ) {U : Set (EuclideanSpace ℝ (Fin d))} (hf : ContinuousOn f U)
    (hkU : closedBall k δ ⊆ U) : Integrable (fun b => f (k + δ • b)) (uniformBall d) := by
  unfold uniformBall
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.2 ?_)
  · apply ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
    refine hf.comp (by fun_prop) ?_
    intro b hb
    apply hkU
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hδ]
    rw [mem_closedBall_zero_iff] at hb
    nlinarith [norm_nonneg b]
  · have : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
      have : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
        rw [finrank_euclideanSpace_fin]; omega
      exact Module.nontrivial_of_finrank_pos this
    rw [Measure.addHaar_closedBall_eq_addHaar_ball]
    exact (measure_ball_pos _ _ one_pos).ne'


theorem mem_cb {d : ℕ} {k v : EuclideanSpace ℝ (Fin d)} {δ : ℝ} (hδ : 0 ≤ δ)
    (hv : v ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) : k + δ • v ∈ closedBall k δ := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hδ]
  rw [mem_closedBall_zero_iff] at hv
  nlinarith [norm_nonneg v]

theorem cl_ball_interior {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} (hSconv : Convex ℝ S)
    {r : ℝ} (hrS : Metric.closedBall 0 r ⊆ S) {α δ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hδα : δ < α * r) : ∀ k ∈ (1 - α) • S, closedBall k δ ⊆ interior S :=
  fun k hk => (closedBall_subset_ball hδα).trans (interior_maximal
    (ball_subset_closedBall.trans (ball_sub S hSconv r hrS α hα0.le hα1 k hk)) isOpen_ball)

theorem smooth_bdd {d : ℕ} (hd : 1 ≤ d) {S : Set (EuclideanSpace ℝ (Fin d))} {C : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfbdd : ∀ x ∈ S, |f x| ≤ C) {k : EuclideanSpace ℝ (Fin d)}
    {δ : ℝ} (hδ : 0 ≤ δ) (hk : closedBall k δ ⊆ S) : |smoothedLoss d δ f k| ≤ C := by
  haveI := uniformBall_prob hd
  have h := norm_integral_le_of_norm_le_const (μ := uniformBall d)
    (f := fun b => f (k + δ • b)) (C := C) (by
      filter_upwards [uniformBall_ae] with b hb
      rw [Real.norm_eq_abs]
      exact hfbdd _ (hk (mem_cb hδ hb)))
  rw [Real.norm_eq_abs] at h
  unfold smoothedLoss
  simpa using h

theorem smooth_convex {d : ℕ} (hd : 1 ≤ d) {S K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : Convex ℝ K) {δ : ℝ} (hδ : 0 ≤ δ) (hKint : ∀ k ∈ K, closedBall k δ ⊆ interior S)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfconv : ConvexOn ℝ S f) :
    ConvexOn ℝ K (smoothedLoss d δ f) := by
  have hcont : ContinuousOn f (interior S) := hfconv.continuousOn_interior
  refine ⟨hK, fun a ha b hb p q hp hq hpq => ?_⟩
  have hab : p • a + q • b ∈ K := hK ha hb hp hq hpq
  have i1 := smooth_integrable hd hδ hcont (hKint _ hab)
  have ia := smooth_integrable hd hδ hcont (hKint _ ha)
  have ib := smooth_integrable hd hδ hcont (hKint _ hb)
  unfold smoothedLoss
  rw [smul_eq_mul, smul_eq_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (ia.const_mul p) (ib.const_mul q)]
  apply integral_mono_ae i1 ((ia.const_mul p).add (ib.const_mul q))
  filter_upwards [uniformBall_ae] with v hv
  have e : p • a + q • b + δ • v = p • (a + δ • v) + q • (b + δ • v) := by
    calc p • a + q • b + δ • v = p • a + q • b + (p + q) • (δ • v) := by rw [hpq, one_smul]
      _ = p • (a + δ • v) + q • (b + δ • v) := by rw [add_smul, smul_add, smul_add]; abel
  have hav : a + δ • v ∈ S := interior_subset (hKint a ha (mem_cb hδ hv))
  have hbv : b + δ • v ∈ S := interior_subset (hKint b hb (mem_cb hδ hv))
  show f (p • a + q • b + δ • v) ≤ p * f (a + δ • v) + q * f (b + δ • v)
  rw [e]
  have := hfconv.2 hav hbv hp hq hpq
  simpa [smul_eq_mul] using this

theorem telescope (a : ℕ → ℝ) (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 n, (a t - a (t + 1)) = a 1 - a (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

open Classical in
theorem smoothed_main {d : ℕ} (hd : 1 ≤ d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (r R : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (hSR : S ⊆ Metric.closedBall 0 R)
    (C : ℝ) (hC : 0 < C) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hum : ∀ t, Measurable (u t))
    (hind : ProbabilityTheory.iIndepFun u P)
    (hlaw : ∀ t, P.map (u t) = RegretBandits.Nonlinear.uniformSphere d)
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (hn : 1 ≤ n) (ν δ α : ℝ) (hν : ν = R / (C * Real.sqrt n))
    (hδ : 0 < δ) (hδα : δ < α * r) (hα1 : α ≤ 1)
    (hrun : ∀ ω, BanditGD.Regret.IsBGDRun S α δ ν c (fun t => u t ω) (fun t => y t ω))
    (hgrad : ∀ t p, closedBall p δ ⊆ interior S →
      HasGradientAt (smoothedLoss d δ (c t))
        (((d : ℝ) / δ) • ∫ v, c t (p + δ • v) • v ∂(uniformSphere d)) p) :
    pseudoRegret ((1 - α) • S) (fun t => smoothedLoss d δ (c t)) P y n
      ≤ R * d * C * Real.sqrt n / δ := by
  have hα0 : 0 < α := by
    by_contra h; push_neg at h; nlinarith
  have h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S := hrS (Metric.mem_closedBall_self hr.le)
  set K := (1 - α) • S with hKdef
  have hK : Convex ℝ K := hSconv.smul _
  have hKc : IsClosed K := hSclosed.smul₀ _
  have h0K : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := ⟨0, h0S, smul_zero _⟩
  have hKne : K.Nonempty := ⟨0, h0K⟩
  have hKR : K ⊆ closedBall 0 R := Kp_sub_ball S R hSR α hα0.le hα1
  have hKint : ∀ k ∈ K, closedBall k δ ⊆ interior S := cl_ball_interior hSconv hrS hα0 hα1 hδα
  have hR : 0 < R := by
    have hm : EuclideanSpace.single (⟨0, hd⟩ : Fin d) r ∈ S :=
      hrS (by rw [mem_closedBall_zero_iff]; simp [abs_of_pos hr])
    have := hSR hm
    rw [mem_closedBall_zero_iff] at this
    simp [abs_of_pos hr] at this
    linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hνpos : 0 < ν := by rw [hν]; positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- measurable truncation of the costs
  set ct : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun t x => if x ∈ interior S then c t x else 0
    with hctdef
  have hct : ∀ t, Measurable (ct t) := fun t =>
    (hcconv t).continuousOn_interior.measurable_piecewise continuousOn_const
      isOpen_interior.measurableSet
  have hctb : ∀ t x, |ct t x| ≤ C := by
    intro t x
    simp only [hctdef]
    split_ifs with h
    · exact hcbdd t x (interior_subset h)
    · simp [hC.le]
  have hctc : ∀ t, ∀ x ∈ interior S, ct t x = c t x := by
    intro t x hx; simp only [hctdef, if_pos hx]
  -- the deterministic version of the run
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun t ω => Yf K ct ν δ t (fun s => u s ω) with hYdef
  have hUm : Measurable (fun ω (s : ℕ) => u s ω) := measurable_pi_lambda _ hum
  have hYm : ∀ t, Measurable (Y t) := fun t =>
    (Yf_measurable hK hKc h0K ct hct ν δ t).comp hUm
  have hYK : ∀ t ω, Y t ω ∈ K := fun t ω => Yf_mem hK hKc h0K ct ν δ _ t
  have hYR : ∀ t ω, ‖Y t ω‖ ≤ R := fun t ω => mem_closedBall_zero_iff.1 (hKR (hYK t ω))
  have hsph : ∀ᵐ v ∂(uniformSphere d), ‖v‖ = 1 := by
    unfold uniformSphere sphereMeasure
    apply Measure.ae_smul_measure
    rw [ae_map_iff measurable_subtype_coe.aemeasurable
      (isClosed_eq continuous_norm continuous_const).measurableSet]
    exact Filter.Eventually.of_forall fun v => mem_sphere_zero_iff_norm.1 v.2
  have hgood : ∀ᵐ ω ∂P, ∀ t, ‖u t ω‖ = 1 := by
    rw [ae_all_iff]
    intro t
    have hs := hsph
    rw [← hlaw t] at hs
    exact ae_of_ae_map (hum t).aemeasurable hs
  have hyY : ∀ᵐ ω ∂P, ∀ t, 1 ≤ t → y t ω = Y t ω := by
    filter_upwards [hgood] with ω hω
    exact run_eq_Yf hSconv hSclosed hr hrS hδ hδα hα1 c _ _ hω (hrun ω)
  -- smoothed losses
  set ch : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun t => smoothedLoss d δ (c t) with hch
  have hchb : ∀ t, ∀ k ∈ K, |ch t k| ≤ C := fun t k hk =>
    smooth_bdd hd (hcbdd t) hδ.le ((hKint k hk).trans interior_subset)
  have hchconv : ∀ t, ConvexOn ℝ K (ch t) := fun t =>
    smooth_convex hd hK hδ.le hKint (hcconv t)
  set O : Set (EuclideanSpace ℝ (Fin d)) := ⋃ k ∈ K, ball k (α * r - δ) with hO
  have hOopen : IsOpen O := isOpen_biUnion fun k _ => isOpen_ball
  have hKO : K ⊆ O := fun k hk => mem_biUnion hk (mem_ball_self (by linarith))
  have hOint : ∀ p ∈ O, closedBall p δ ⊆ interior S := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.1 hp
    intro q hq
    apply interior_maximal (ball_subset_closedBall.trans
      (ball_sub S hSconv r hrS α hα0.le hα1 k hk)) isOpen_ball
    rw [mem_ball] at hpk ⊢
    rw [mem_closedBall] at hq
    linarith [dist_triangle q p k]
  have hchcont : ∀ t, ContinuousOn (ch t) O := fun t p hp =>
    (hgrad t p (hOint p hp)).differentiableAt.continuousAt.continuousWithinAt
  have hchY : ∀ t, Measurable (fun ω => ch t (Y t ω)) := by
    intro t
    have hm : Measurable (O.piecewise (ch t) (fun _ => 0)) :=
      (hchcont t).measurable_piecewise continuousOn_const hOopen.measurableSet
    have : (fun ω => ch t (Y t ω)) = fun ω => O.piecewise (ch t) (fun _ => 0) (Y t ω) := by
      funext ω; rw [Set.piecewise_eq_of_mem _ _ _ (hKO (hYK t ω))]
    rw [this]; exact hm.comp (hYm t)
  have hchYi : ∀ t, Integrable (fun ω => ch t (Y t ω)) P := fun t =>
    (integrable_const C).mono' (hchY t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hchb t _ (hYK t ω))
  -- independence of the current point and the current direction
  have hindt : ∀ t, ProbabilityTheory.IndepFun (Y t) (u t) P := by
    intro t
    have h1 := hind.indepFun_finset (Finset.range t) {t}
      (Finset.disjoint_singleton_right.2 (by simp)) hum
    have hext : Measurable (fun v : (Finset.range t) → EuclideanSpace ℝ (Fin d) =>
        fun s => if h : s ∈ Finset.range t then v ⟨s, h⟩ else 0) := by
      apply measurable_pi_lambda
      intro s
      by_cases h : s ∈ Finset.range t
      · simp only [h, dif_pos]; exact measurable_pi_apply _
      · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const
    have hY' : Y t = (fun v : (Finset.range t) → EuclideanSpace ℝ (Fin d) =>
        Yf K ct ν δ t (fun s => if h : s ∈ Finset.range t then v ⟨s, h⟩ else 0)) ∘
          (fun ω (i : Finset.range t) => u i ω) := by
      funext ω
      simp only [Function.comp, hYdef]
      apply Yf_local
      intro s hs
      simp [Finset.mem_range.2 hs]
    have hU' : u t = (fun v : ({t} : Finset ℕ) → EuclideanSpace ℝ (Fin d) =>
        v ⟨t, Finset.mem_singleton_self t⟩) ∘ (fun ω (i : ({t} : Finset ℕ)) => u i ω) := rfl
    rw [hY', hU']
    exact h1.comp ((Yf_measurable hK hKc h0K ct hct ν δ t).comp hext) (measurable_pi_apply _)
  -- main estimate for a fixed comparator
  have main : ∀ z ∈ K, (∫ ω, ∑ t ∈ Finset.Icc 1 n, ch t (Y t ω) ∂P) -
      ∑ t ∈ Finset.Icc 1 n, ch t z ≤ R * d * C * Real.sqrt n / δ := by
    intro z hz
    have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 (hKR hz)
    have hνne := hνpos.ne'
    have hδne := hδ.ne'
    have hCne := hC.ne'
    have hsne := hsqrt.ne'
    have hdne := hdpos.ne'
    set D : ℕ → Ω → ℝ := fun t ω => ‖Y t ω - z‖ ^ 2 with hDdef
    set G : ℕ → Ω → ℝ := fun t ω => ct t (Y t ω + δ • u t ω) * inner ℝ (u t ω) (Y t ω - z)
      with hGdef
    have hYz : ∀ t ω, ‖Y t ω - z‖ ≤ 2 * R := fun t ω =>
      (norm_sub_le _ _).trans (by linarith [hYR t ω])
    have hDi : ∀ t, Integrable (D t) P := fun t =>
      (integrable_const ((2 * R) ^ 2)).mono'
        (((hYm t).sub_const z).norm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hYz t ω) 2)
    set cl : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
      fun v => if ‖v‖ ≤ 1 then v else 0 with hcl
    have hclm : Measurable cl :=
      Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
        measurable_const
    have hcl1 : ∀ v, ‖cl v‖ ≤ 1 := by
      intro v; simp only [hcl]; split_ifs with h
      · exact h
      · simp
    have hpc := proj_continuous hK hKc hKne
    have hprojK : ∀ k, proj K k ∈ K := fun k => (proj_spec hK hKc hKne k).1
    have hprojid : ∀ k ∈ K, proj K k = k := fun k hk =>
      proj_eq hK hKc hKne ⟨hk, fun w _ => by simp⟩
    set F : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ :=
      fun t p => ct t (proj K p.1 + δ • p.2) * inner ℝ (cl p.2) (proj K p.1 - z) with hFdef
    have hFm : ∀ t, Measurable (F t) := fun t =>
      ((hct t).comp ((hpc.measurable.comp measurable_fst).add (measurable_snd.const_smul δ))).mul
        ((hclm.comp measurable_snd).inner ((hpc.measurable.comp measurable_fst).sub_const z))
    have hFb : ∀ t p, |F t p| ≤ C * (2 * R) := by
      intro t p
      simp only [hFdef]
      rw [abs_mul]
      have h1 := hctb t (proj K p.1 + δ • p.2)
      have h2 : |inner ℝ (cl p.2) (proj K p.1 - z)| ≤ 2 * R := by
        calc _ ≤ ‖cl p.2‖ * ‖proj K p.1 - z‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * (2 * R) := mul_le_mul (hcl1 _)
              ((norm_sub_le _ _).trans
                (by linarith [mem_closedBall_zero_iff.1 (hKR (hprojK p.1))]))
              (norm_nonneg _) zero_le_one
          _ = 2 * R := one_mul _
      exact mul_le_mul h1 h2 (abs_nonneg _) hC.le
    have hGF : ∀ t, G t =ᵐ[P] fun ω => F t (Y t ω, u t ω) := by
      intro t
      filter_upwards [hgood] with ω hω
      have : cl (u t ω) = u t ω := by simp only [hcl, if_pos (le_of_eq (hω t))]
      simp only [hGdef, hFdef, hprojid _ (hYK t ω), this]
    have hGi : ∀ t, Integrable (G t) P := fun t =>
      ((integrable_const (C * (2 * R))).mono'
        ((hFm t).comp ((hYm t).prodMk (hum t))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact hFb t _)).congr (hGF t).symm
    -- (A) projection step
    have hstep : ∀ t, 1 ≤ t → ∀ᵐ ω ∂P,
        2 * ν * G t ω ≤ D t ω - D (t + 1) ω + ν ^ 2 * C ^ 2 := by
      intro t ht
      filter_upwards [hgood] with ω hω
      set a := ν * ct t (Y t ω + δ • u t ω) with ha
      have hY1 : Y (t + 1) ω = proj K (Y t ω - a • u t ω) := Yf_succ _ _ _ _ _ ht
      have hne := nearest_nonexp hK (proj_spec hK hKc hKne (Y t ω - a • u t ω)) hz
      rw [← hY1] at hne
      have e : Y t ω - a • u t ω - z = (Y t ω - z) - a • u t ω := by abel
      rw [e, norm_sub_sq_real (x := Y t ω - z) (y := a • u t ω), inner_smul_right, norm_smul,
        Real.norm_eq_abs, hω t, mul_one, sq_abs] at hne
      have ha2 : a ^ 2 ≤ ν ^ 2 * C ^ 2 := by
        have h1 := hctb t (Y t ω + δ • u t ω)
        have h2 : (ct t (Y t ω + δ • u t ω)) ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [ha, mul_pow]
        exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      have hG : 2 * ν * G t ω = 2 * (a * inner ℝ (Y t ω - z) (u t ω)) := by
        simp only [hGdef, ha, real_inner_comm (u t ω)]; ring
      simp only [hDdef]
      rw [hG]
      linarith
    -- (B) expectation of G via independence and the smoothing gradient
    have hEG : ∀ t, 1 ≤ t → δ / d * ((∫ ω, ch t (Y t ω) ∂P) - ch t z) ≤ ∫ ω, G t ω ∂P := by
      intro t ht
      haveI hUprob : IsProbabilityMeasure (uniformSphere d) := by
        rw [← hlaw 0]; exact Measure.isProbabilityMeasure_map (hum 0).aemeasurable
      have hI : ∀ k ∈ K, δ / d * (ch t k - ch t z) ≤ ∫ v, F t (k, v) ∂(uniformSphere d) := by
        intro k hk
        set Γ := ∫ v, c t (k + δ • v) • v ∂(uniformSphere d) with hΓ
        have hgi := grad_ineq (hchconv t) hk hz (hgrad t k (hKint k hk))
        rw [← hΓ, real_inner_smul_left] at hgi
        have hin : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 → k + δ • v ∈ interior S := fun v hv =>
          hKint k hk (mem_cb hδ.le (by rw [mem_closedBall_zero_iff, hv]))
        have hFk : (fun v => F t (k, v)) =ᵐ[uniformSphere d]
            fun v => inner ℝ (k - z) (c t (k + δ • v) • v) := by
          filter_upwards [hsph] with v hv
          have hclv : cl v = v := by simp only [hcl, if_pos (le_of_eq hv)]
          simp only [hFdef, hprojid k hk, hctc t _ (hin v hv), hclv, real_inner_smul_right,
            real_inner_comm v]
        have hint : Integrable (fun v => c t (k + δ • v) • v) (uniformSphere d) := by
          have hm : Measurable (fun v => ct t (k + δ • v) • v) :=
            ((hct t).comp (measurable_const.add (measurable_id.const_smul δ))).smul measurable_id
          refine ((integrable_const C).mono' hm.aestronglyMeasurable ?_).congr ?_
          · filter_upwards [hsph] with v hv
            rw [norm_smul, hv, mul_one, Real.norm_eq_abs]; exact hctb t _
          · filter_upwards [hsph] with v hv
            simp only [hctc t _ (hin v hv)]
        rw [integral_congr_ae hFk, integral_inner hint, ← hΓ]
        have e : inner ℝ (k - z) Γ = - inner ℝ Γ (z - k) := by
          rw [real_inner_comm, ← inner_neg_right, neg_sub]
        rw [e]
        have hdδ : 0 < (d : ℝ) / δ := by positivity
        have h4 : inner ℝ Γ (z - k) ≤ (ch t z - ch t k) / ((d : ℝ) / δ) := by
          rw [le_div_iff₀ hdδ]; linarith
        have h5 : (ch t z - ch t k) / ((d : ℝ) / δ) = δ / d * (ch t z - ch t k) := by
          field_simp
        rw [h5] at h4
        linarith
      have hIm : Measurable (fun k => ∫ v, F t (k, v) ∂(P.map (u t))) :=
        (hFm t).stronglyMeasurable.integral_prod_right'.measurable
      haveI : IsProbabilityMeasure (P.map (u t)) :=
        Measure.isProbabilityMeasure_map (hum t).aemeasurable
      have hIi : Integrable (fun ω => ∫ v, F t (Y t ω, v) ∂(P.map (u t))) P := by
        refine (integrable_const (C * (2 * R))).mono' (hIm.comp (hYm t)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => ?_)
        have := norm_integral_le_of_norm_le_const (μ := P.map (u t))
          (f := fun v => F t (Y t ω, v)) (C := C * (2 * R))
          (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hFb t _)
        simpa using this
      rw [integral_congr_ae (hGF t),
        indep_integral P (hYm t) (hum t) (hindt t) (F t) (hFm t) _ (hFb t)]
      have hL : ∫ ω, δ / d * (ch t (Y t ω) - ch t z) ∂P =
          δ / d * ((∫ ω, ch t (Y t ω) ∂P) - ch t z) := by
        rw [integral_const_mul, integral_sub (hchYi t) (integrable_const _), integral_const]
        simp
      rw [← hL]
      refine integral_mono (((hchYi t).sub (integrable_const _)).const_mul _) hIi fun ω => ?_
      show δ / d * (ch t (Y t ω) - ch t z) ≤ ∫ v, F t (Y t ω, v) ∂(P.map (u t))
      rw [hlaw t]
      exact hI _ (hYK t ω)
    -- (C) combine
    have hstepE : ∀ t, 1 ≤ t → 2 * ν * ∫ ω, G t ω ∂P ≤
        (∫ ω, D t ω ∂P) - (∫ ω, D (t + 1) ω ∂P) + ν ^ 2 * C ^ 2 := by
      intro t ht
      have i1 : Integrable (fun ω => D t ω - D (t + 1) ω) P := (hDi t).sub (hDi (t + 1))
      have i2 : Integrable (fun ω => D t ω - D (t + 1) ω + ν ^ 2 * C ^ 2) P :=
        i1.add (integrable_const _)
      have i3 : Integrable (fun ω => 2 * ν * G t ω) P := (hGi t).const_mul _
      have h := integral_mono_ae i3 i2 (hstep t ht)
      rw [integral_const_mul, integral_add i1 (integrable_const _),
        integral_sub (hDi t) (hDi (t + 1)), integral_const] at h
      simpa using h
    have hper : ∀ t, 1 ≤ t → (∫ ω, ch t (Y t ω) ∂P) - ch t z ≤
        d / (2 * ν * δ) * ((∫ ω, D t ω ∂P) - (∫ ω, D (t + 1) ω ∂P) + ν ^ 2 * C ^ 2) := by
      intro t ht
      have h1 := hEG t ht
      have h2 := hstepE t ht
      have hEGle : ∫ ω, G t ω ∂P ≤
          ((∫ ω, D t ω ∂P) - (∫ ω, D (t + 1) ω ∂P) + ν ^ 2 * C ^ 2) / (2 * ν) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hX : (∫ ω, ch t (Y t ω) ∂P) - ch t z ≤ (d / δ) * ∫ ω, G t ω ∂P := by
        have := mul_le_mul_of_nonneg_left h1 (le_of_lt (by positivity : (0 : ℝ) < d / δ))
        rwa [← mul_assoc, show (d : ℝ) / δ * (δ / d) = 1 by field_simp, one_mul] at this
      calc (∫ ω, ch t (Y t ω) ∂P) - ch t z ≤ (d / δ) * ∫ ω, G t ω ∂P := hX
        _ ≤ (d / δ) * (((∫ ω, D t ω ∂P) - (∫ ω, D (t + 1) ω ∂P) + ν ^ 2 * C ^ 2) / (2 * ν)) :=
            mul_le_mul_of_nonneg_left hEGle (by positivity)
        _ = d / (2 * ν * δ) * ((∫ ω, D t ω ∂P) - (∫ ω, D (t + 1) ω ∂P) + ν ^ 2 * C ^ 2) := by
            field_simp
    have hsum := Finset.sum_le_sum (s := Finset.Icc 1 n) fun t ht => hper t (Finset.mem_Icc.1 ht).1
    rw [← Finset.mul_sum, Finset.sum_add_distrib,
      telescope (fun t => ∫ ω, D t ω ∂P) n, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul] at hsum
    have hD1 : ∫ ω, D 1 ω ∂P ≤ R ^ 2 := by
      have : ∀ ω, D 1 ω = ‖z‖ ^ 2 := by
        intro ω; simp [hDdef, hYdef, Yf, norm_neg]
      simp only [this, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) hzR 2
    have hDn : 0 ≤ ∫ ω, D (n + 1) ω ∂P := integral_nonneg fun ω => sq_nonneg _
    rw [integral_finset_sum _ (fun t _ => hchYi t), ← Finset.sum_sub_distrib]
    have hcoef : 0 < (d : ℝ) / (2 * ν * δ) := by positivity
    have hR' : R = ν * C * Real.sqrt n := by rw [hν]; field_simp
    have hnss : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hnpos.le).symm
    calc _ ≤ d / (2 * ν * δ) * ((∫ ω, D 1 ω ∂P) - (∫ ω, D (n + 1) ω ∂P) +
          n * (ν ^ 2 * C ^ 2)) := hsum
      _ ≤ d / (2 * ν * δ) * (R ^ 2 + n * (ν ^ 2 * C ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hcoef.le
      _ = R * d * C * Real.sqrt n / δ := by
          rw [hR']
          have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
          generalize Real.sqrt (n : ℝ) = s at hss ⊢
          rw [← hss]; field_simp; ring
  -- conclusion
  unfold pseudoRegret
  have hcongr : ∫ ω, ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) (y t ω) ∂P =
      ∫ ω, ∑ t ∈ Finset.Icc 1 n, ch t (Y t ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [hyY] with ω hω
    exact Finset.sum_congr rfl fun t ht => by rw [hω t (Finset.mem_Icc.1 ht).1]
  rw [hcongr]
  haveI : Nonempty K := ⟨⟨0, h0K⟩⟩
  have hle : (∫ ω, ∑ t ∈ Finset.Icc 1 n, ch t (Y t ω) ∂P) - R * d * C * Real.sqrt n / δ ≤
      ⨅ x : K, ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) x :=
    le_ciInf fun x => by linarith [main x x.2]
  linarith

end BGDL2

open scoped Pointwise

set_option autoImplicit false


theorem BanditGD_obs1_pt {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S) (C : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hconv : ConvexOn ℝ S f) (hbdd : ∀ x ∈ S, |f x| ≤ C)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ S) :
    f ((1 - α) • x) ≤ f x + 2 * α * C := by
  have h := hconv.2 hx h0S (show (0:ℝ) ≤ 1 - α by linarith) hα0 (show 1 - α + α = 1 by ring)
  simp only [smul_zero, add_zero, smul_eq_mul] at h
  have h1 := abs_le.mp (hbdd x hx)
  have h2 := abs_le.mp (hbdd 0 h0S)
  have h3 : α * (f 0 - f x) ≤ α * (2 * C) :=
    mul_le_mul_of_nonneg_left (by linarith) hα0
  nlinarith

open scoped Pointwise in
theorem obs1_sol {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S) (C : ℝ) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    (⨅ x : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))), ∑ t ∈ Finset.Icc 1 n, c t x)
      ≤ 2 * α * C * n + ⨅ x : S, ∑ t ∈ Finset.Icc 1 n, c t x := by
  have hsub : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))) ⊆ S := by
    rintro y ⟨x, hx, rfl⟩
    exact hSconv.smul_mem_of_zero_mem h0S hx ⟨by linarith, by linarith⟩
  have hlow : ∀ x ∈ S, -(n * C) ≤ ∑ t ∈ Finset.Icc 1 n, c t x := by
    intro x hx
    have : ∑ t ∈ Finset.Icc 1 n, (-C) ≤ ∑ t ∈ Finset.Icc 1 n, c t x :=
      Finset.sum_le_sum fun t _ => (abs_le.mp (hcbdd t x hx)).1
    simpa [Finset.sum_const, Nat.card_Icc] using this
  have hbdd : BddBelow (Set.range fun x : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))) =>
      ∑ t ∈ Finset.Icc 1 n, c t x) := by
    refine ⟨-(n * C), ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hlow y (hsub y.2)
  have : Nonempty S := ⟨⟨0, h0S⟩⟩
  have key : ∀ x : S, (⨅ x : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))),
      ∑ t ∈ Finset.Icc 1 n, c t x) - 2 * α * C * n ≤ ∑ t ∈ Finset.Icc 1 n, c t x := by
    rintro ⟨x, hx⟩
    have hmem : (1 - α) • x ∈ ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))) :=
      Set.smul_mem_smul_set hx
    have h1 := ciInf_le hbdd ⟨(1 - α) • x, hmem⟩
    have h2 : ∑ t ∈ Finset.Icc 1 n, c t ((1 - α) • x) ≤
        ∑ t ∈ Finset.Icc 1 n, (c t x + 2 * α * C) :=
      Finset.sum_le_sum fun t _ =>
        BanditGD_obs1_pt S h0S C (c t) (hcconv t) (hcbdd t) α hα0 hα1 x hx
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc] at h2
    simp only [nsmul_eq_mul, Nat.add_sub_cancel] at h2
    simp only at h1 ⊢
    nlinarith
  have := le_ciInf key
  linarith

open scoped Pointwise

set_option autoImplicit false

namespace P96e24d05

lemma ball_sub {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hrS : Metric.closedBall 0 r ⊆ S) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ (1 - α) • S) (w : EuclideanSpace ℝ (Fin d))
    (hw : ‖w - x‖ ≤ α * r) : w ∈ S := by
  obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.mp hx
  have hz : α⁻¹ • (w - (1 - α) • s) ∈ S := by
    apply hrS
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hα0, inv_mul_le_iff₀ hα0]
    exact hw
  have := hSconv hs hz (by linarith : (0:ℝ) ≤ 1 - α) hα0.le (by ring)
  convert this using 1
  rw [smul_smul, mul_inv_cancel₀ hα0.ne', one_smul]
  abel

end P96e24d05

open scoped Pointwise in
theorem obs3_sol {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (C : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ S f) (hfC : ∀ x ∈ S, |f x| ≤ C) :
    ∀ x ∈ (1 - α) • S, ∀ y ∈ S, |f x - f y| ≤ 2 * C / (α * r) * ‖x - y‖ := by
  intro x hx y hy
  have hρ : 0 < α * r := mul_pos hα0 hr
  set ρ := α * r with hρdef
  have hxS : x ∈ S := P96e24d05.ball_sub S hSconv r hrS α hα0 hα1 x hx x (by simpa using hρ.le)
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hfC x hxS)
  have bnd : ∀ u ∈ S, ∀ v ∈ S, f u - f v ≤ 2 * C := by
    intro u hu v hv
    have h1 := (abs_le.mp (hfC u hu)).2
    have h2 := (abs_le.mp (hfC v hv)).1
    linarith
  set t := ‖x - y‖ with htdef
  rcases (norm_nonneg (x - y)).eq_or_lt with h0 | ht
  · have hxy : x = y := sub_eq_zero.mp (norm_eq_zero.mp h0.symm)
    have ht0 : t = 0 := h0.symm
    rw [ht0, mul_zero, hxy, sub_self, abs_zero]
  have ht : 0 < t := ht
  have htne : t ≠ 0 := ht.ne'
  have hρt : ρ + t ≠ 0 := by positivity
  have hrw : 2 * C / ρ * t = 2 * C * (t / ρ) := by ring
  rw [hrw, abs_sub_le_iff]
  constructor
  · -- f x - f y
    set z := x + (ρ / t) • (x - y) with hzdef
    have hzS : z ∈ S := by
      apply P96e24d05.ball_sub S hSconv r hrS α hα0 hα1 x hx z
      rw [hzdef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ ht),
        ← htdef, div_mul_cancel₀ _ ht.ne']
    have hsum : ρ / (ρ + t) + t / (ρ + t) = 1 := by
      field_simp
    have hcomb : (ρ / (ρ + t)) • y + (t / (ρ + t)) • z = x := by
      have e : (ρ / (ρ + t)) • y + (t / (ρ + t)) • z
          = ((t / (ρ + t)) + (t / (ρ + t)) * (ρ / t)) • x
            + ((ρ / (ρ + t)) - (t / (ρ + t)) * (ρ / t)) • y := by
        rw [hzdef]; module
      have c1 : (t / (ρ + t)) + (t / (ρ + t)) * (ρ / t) = 1 := by
        field_simp
        ring
      have c2 : (ρ / (ρ + t)) - (t / (ρ + t)) * (ρ / t) = 0 := by
        field_simp; ring
      rw [e, c1, c2, one_smul, zero_smul, add_zero]
    have hconv := hf.2 hy hzS (div_pos hρ (by linarith)).le (div_pos ht (by linarith)).le hsum
    rw [hcomb, smul_eq_mul, smul_eq_mul] at hconv
    have hb : t / (ρ + t) ≤ t / ρ := div_le_div_of_nonneg_left ht.le hρ (by linarith)
    have hzy := bnd z hzS y hy
    have ha : ρ / (ρ + t) = 1 - t / (ρ + t) := by linarith
    rw [ha] at hconv
    have hb0 : 0 ≤ t / (ρ + t) := (div_pos ht (by linarith)).le
    nlinarith
  · -- f y - f x
    rcases le_or_gt ρ t with hle | hlt
    · have h1 : 1 ≤ t / ρ := (one_le_div hρ).mpr hle
      have := bnd y hy x hxS
      nlinarith
    · set w := x + (ρ / t) • (y - x) with hwdef
      have hwS : w ∈ S := by
        apply P96e24d05.ball_sub S hSconv r hrS α hα0 hα1 x hx w
        rw [hwdef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ ht),
          norm_sub_rev, ← htdef, div_mul_cancel₀ _ ht.ne']
      have hcomb : (1 - t / ρ) • x + (t / ρ) • w = y := by
        have e : (1 - t / ρ) • x + (t / ρ) • w
            = (1 - t / ρ + t / ρ - (t / ρ) * (ρ / t)) • x + ((t / ρ) * (ρ / t)) • y := by
          rw [hwdef]; module
        have c1 : (t / ρ) * (ρ / t) = 1 := by field_simp
        rw [e, c1, one_smul, sub_add_cancel, sub_self, zero_smul, zero_add]
      have h1 : 0 ≤ 1 - t / ρ := by
        have : t / ρ < 1 := (div_lt_one hρ).mpr hlt
        linarith
      have hsum : (1 - t / ρ) + t / ρ = 1 := by ring
      have hconv := hf.2 hxS hwS h1 (div_pos ht hρ).le hsum
      rw [hcomb, smul_eq_mul, smul_eq_mul] at hconv
      have := bnd w hwS x hxS
      nlinarith [div_pos ht hρ]


namespace BGDL3

open MeasureTheory Set Metric RegretBandits.Nonlinear BGDL2
open scoped Pointwise

open Classical in
theorem eq10_main {d : ℕ} (hd : 1 ≤ d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (r R : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (hSR : S ⊆ Metric.closedBall 0 R)
    (C : ℝ) (hC : 0 < C) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hum : ∀ t, Measurable (u t))
    (hind : ProbabilityTheory.iIndepFun u P)
    (hlaw : ∀ t, P.map (u t) = RegretBandits.Nonlinear.uniformSphere d)
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (hn : 1 ≤ n) (ν δ α : ℝ) (hν : ν = R / (C * Real.sqrt n))
    (hδ : 0 < δ) (hδα : δ < α * r) (hα1 : α ≤ 1)
    (hrun : ∀ ω, BanditGD.Regret.IsBGDRun S α δ ν c (fun t => u t ω) (fun t => y t ω)) :
    RegretBandits.Nonlinear.pseudoRegret S c P (fun t ω => y t ω + δ • u t ω) n
      ≤ R * d * C * Real.sqrt n / δ + 3 * δ * (2 * C / (α * r)) * n + 2 * α * C * n := by
  have hα0 : 0 < α := by
    by_contra h; push_neg at h; nlinarith
  have h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S := hrS (Metric.mem_closedBall_self hr.le)
  set K := (1 - α) • S with hKdef
  have hK : Convex ℝ K := hSconv.smul _
  have hKc : IsClosed K := hSclosed.smul₀ _
  have h0K : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := ⟨0, h0S, smul_zero _⟩
  have hKint : ∀ k ∈ K, closedBall k δ ⊆ interior S := cl_ball_interior hSconv hrS hα0 hα1 hδα
  set L : ℝ := 2 * C / (α * r) with hLdef
  have hL : 0 ≤ L := by positivity
  have hgrad : ∀ t p, closedBall p δ ⊆ interior S →
      HasGradientAt (smoothedLoss d δ (c t))
        (((d : ℝ) / δ) • ∫ v, c t (p + δ • v) • v ∂(uniformSphere d)) p :=
    fun t p hp => BGDL1.lemma1_gen hd (c t) δ hδ p (interior S) isOpen_interior hp
      (hcconv t).continuousOn_interior
  have hSM := smoothed_main hd S hSconv hSclosed r R hr hrS hSR C hC c hcconv hcbdd P u hum hind
    hlaw y n hn ν δ α hν hδ hδα hα1 hrun hgrad
  have hlip : ∀ t, ∀ x ∈ K, ∀ w ∈ S, |c t x - c t w| ≤ L * ‖x - w‖ := fun t =>
    obs3_sol S hSconv r hr hrS α hα0 hα1 C (c t) (hcconv t) (hcbdd t)
  have hsm : ∀ t, ∀ k ∈ K, |smoothedLoss d δ (c t) k - c t k| ≤ L * δ := by
    intro t k hk
    haveI := uniformBall_prob hd
    have hint := smooth_integrable hd hδ.le (hcconv t).continuousOn_interior (hKint k hk)
    have e : smoothedLoss d δ (c t) k - c t k = ∫ b, (c t (k + δ • b) - c t k) ∂(uniformBall d) := by
      rw [integral_sub hint (integrable_const _), integral_const]
      simp [smoothedLoss]
    rw [e]
    have h := norm_integral_le_of_norm_le_const (μ := uniformBall d)
      (f := fun b => c t (k + δ • b) - c t k) (C := L * δ) (by
        filter_upwards [uniformBall_ae] with b hb
        rw [Real.norm_eq_abs, abs_sub_comm]
        have hw : k + δ • b ∈ S := interior_subset (hKint k hk (mem_cb hδ.le hb))
        calc |c t k - c t (k + δ • b)| ≤ L * ‖k - (k + δ • b)‖ := hlip t k hk _ hw
          _ ≤ L * δ := by
            apply mul_le_mul_of_nonneg_left _ hL
            rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
            rw [mem_closedBall_zero_iff] at hb
            nlinarith [norm_nonneg b])
    rw [Real.norm_eq_abs] at h
    simpa using h
  -- the deterministic run and the good set (as in smoothed_main)
  set ct : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun t x => if x ∈ interior S then c t x else 0
    with hctdef
  have hct : ∀ t, Measurable (ct t) := fun t =>
    (hcconv t).continuousOn_interior.measurable_piecewise continuousOn_const
      isOpen_interior.measurableSet
  have hctb : ∀ t x, |ct t x| ≤ C := by
    intro t x
    simp only [hctdef]
    split_ifs with h
    · exact hcbdd t x (interior_subset h)
    · simp [hC.le]
  have hctc : ∀ t, ∀ x ∈ interior S, ct t x = c t x := by
    intro t x hx; simp only [hctdef, if_pos hx]
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun t ω => Yf K ct ν δ t (fun s => u s ω) with hYdef
  have hUm : Measurable (fun ω (s : ℕ) => u s ω) := measurable_pi_lambda _ hum
  have hYm : ∀ t, Measurable (Y t) := fun t =>
    (Yf_measurable hK hKc h0K ct hct ν δ t).comp hUm
  have hYK : ∀ t ω, Y t ω ∈ K := fun t ω => Yf_mem hK hKc h0K ct ν δ _ t
  have hsph : ∀ᵐ v ∂(uniformSphere d), ‖v‖ = 1 := by
    unfold uniformSphere sphereMeasure
    apply Measure.ae_smul_measure
    rw [ae_map_iff measurable_subtype_coe.aemeasurable
      (isClosed_eq continuous_norm continuous_const).measurableSet]
    exact Filter.Eventually.of_forall fun v => mem_sphere_zero_iff_norm.1 v.2
  have hgood : ∀ᵐ ω ∂P, ∀ t, ‖u t ω‖ = 1 := by
    rw [ae_all_iff]
    intro t
    have hs := hsph
    rw [← hlaw t] at hs
    exact ae_of_ae_map (hum t).aemeasurable hs
  have hyY : ∀ᵐ ω ∂P, ∀ t, 1 ≤ t → y t ω = Y t ω := by
    filter_upwards [hgood] with ω hω
    exact run_eq_Yf hSconv hSclosed hr hrS hδ hδα hα1 c _ _ hω (hrun ω)
  have hplay : ∀ ω, (∀ t, ‖u t ω‖ = 1) → ∀ t, Y t ω + δ • u t ω ∈ interior S := by
    intro ω hω t
    apply hKint _ (hYK t ω)
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hω t, mul_one,
      Real.norm_eq_abs, abs_of_pos hδ]
  -- integrability of both sums
  have hx_int : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 n, c t (y t ω + δ • u t ω)) P := by
    have hm : Measurable fun ω => ∑ t ∈ Finset.Icc 1 n, ct t (Y t ω + δ • u t ω) :=
      Finset.measurable_sum _ fun t _ => (hct t).comp ((hYm t).add ((hum t).const_smul δ))
    refine ((integrable_const ((n : ℝ) * C)).mono' hm.aestronglyMeasurable ?_).congr ?_
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      calc |∑ t ∈ Finset.Icc 1 n, ct t (Y t ω + δ • u t ω)|
          ≤ ∑ t ∈ Finset.Icc 1 n, |ct t (Y t ω + δ • u t ω)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Finset.Icc 1 n, C := Finset.sum_le_sum fun t _ => hctb t _
        _ = n * C := by simp
    · filter_upwards [hgood, hyY] with ω hω hyω
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hyω t (Finset.mem_Icc.1 ht).1, hctc t _ (hplay ω hω t)]
  set O : Set (EuclideanSpace ℝ (Fin d)) := ⋃ k ∈ K, ball k (α * r - δ) with hO
  have hOopen : IsOpen O := isOpen_biUnion fun k _ => isOpen_ball
  have hKO : K ⊆ O := fun k hk => mem_biUnion hk (mem_ball_self (by linarith))
  have hOint : ∀ p ∈ O, closedBall p δ ⊆ interior S := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.1 hp
    intro q hq
    apply interior_maximal (ball_subset_closedBall.trans
      (ball_sub S hSconv r hrS α hα0.le hα1 k hk)) isOpen_ball
    rw [mem_ball] at hpk ⊢
    rw [mem_closedBall] at hq
    linarith [dist_triangle q p k]
  have hchb : ∀ t, ∀ k ∈ K, |smoothedLoss d δ (c t) k| ≤ C := fun t k hk =>
    smooth_bdd hd (hcbdd t) hδ.le ((hKint k hk).trans interior_subset)
  have hchY : ∀ t, Measurable (fun ω => smoothedLoss d δ (c t) (Y t ω)) := by
    intro t
    have hcont : ContinuousOn (smoothedLoss d δ (c t)) O := fun p hp =>
      (hgrad t p (hOint p hp)).differentiableAt.continuousAt.continuousWithinAt
    have hm : Measurable (O.piecewise (smoothedLoss d δ (c t)) (fun _ => 0)) :=
      hcont.measurable_piecewise continuousOn_const hOopen.measurableSet
    have : (fun ω => smoothedLoss d δ (c t) (Y t ω)) =
        fun ω => O.piecewise (smoothedLoss d δ (c t)) (fun _ => 0) (Y t ω) := by
      funext ω; rw [Set.piecewise_eq_of_mem _ _ _ (hKO (hYK t ω))]
    rw [this]; exact hm.comp (hYm t)
  have hy_int : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) (y t ω)) P := by
    have hm : Measurable fun ω => ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) (Y t ω) :=
      Finset.measurable_sum _ fun t _ => hchY t
    refine ((integrable_const ((n : ℝ) * C)).mono' hm.aestronglyMeasurable ?_).congr ?_
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      calc |∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) (Y t ω)|
          ≤ ∑ t ∈ Finset.Icc 1 n, |smoothedLoss d δ (c t) (Y t ω)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Finset.Icc 1 n, C := Finset.sum_le_sum fun t _ => hchb t _ (hYK t ω)
        _ = n * C := by simp
    · filter_upwards [hyY] with ω hyω
      exact Finset.sum_congr rfl fun t ht => by rw [hyω t (Finset.mem_Icc.1 ht).1]
  -- pointwise comparison along the run
  have hpt : ∀ᵐ ω ∂P, ∑ t ∈ Finset.Icc 1 n, c t (y t ω + δ • u t ω) ≤
      ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) (y t ω) + 2 * L * δ * n := by
    filter_upwards [hgood, hyY] with ω hω hyω
    have key : ∀ t ∈ Finset.Icc 1 n,
        c t (y t ω + δ • u t ω) ≤ smoothedLoss d δ (c t) (y t ω) + 2 * L * δ := by
      intro t ht
      have ht1 := (Finset.mem_Icc.1 ht).1
      have hyK : y t ω ∈ K := by rw [hyω t ht1]; exact hYK t ω
      have hw : y t ω + δ • u t ω ∈ S := by
        rw [hyω t ht1]; exact interior_subset (hplay ω hω t)
      have h1 := hlip t _ hyK _ hw
      rw [sub_add_cancel_left, norm_neg, norm_smul, hω t, mul_one, Real.norm_eq_abs,
        abs_of_pos hδ] at h1
      have h2 := hsm t _ hyK
      rw [abs_le] at h1 h2
      linarith [h1.1, h2.1]
    calc ∑ t ∈ Finset.Icc 1 n, c t (y t ω + δ • u t ω)
        ≤ ∑ t ∈ Finset.Icc 1 n, (smoothedLoss d δ (c t) (y t ω) + 2 * L * δ) :=
          Finset.sum_le_sum key
      _ = ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) (y t ω) + 2 * L * δ * n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
            nsmul_eq_mul]
          ring
  have i2 : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) (y t ω) +
      2 * L * δ * n) P := hy_int.add (integrable_const _)
  have hint_le := integral_mono_ae hx_int i2 hpt
  rw [integral_add hy_int (integrable_const _), integral_const] at hint_le
  simp only [probReal_univ, smul_eq_mul, one_mul] at hint_le
  -- infimum comparisons
  have hobs1 := obs1_sol S hSconv h0S C c hcconv hcbdd α hα0.le hα1 n
  haveI : Nonempty K := ⟨⟨0, h0K⟩⟩
  have hinfK : (⨅ x : K, ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) x) - L * δ * n ≤
      ⨅ x : K, ∑ t ∈ Finset.Icc 1 n, c t x := by
    apply le_ciInf
    intro x
    have hbdd : BddBelow (Set.range fun x : K => ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) x) := by
      refine ⟨-((n : ℝ) * C), ?_⟩
      rintro _ ⟨w, rfl⟩
      have : ∑ t ∈ Finset.Icc 1 n, (-C) ≤ ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) w :=
        Finset.sum_le_sum fun t _ => (abs_le.1 (hchb t w w.2)).1
      simpa using this
    have h1 := ciInf_le hbdd x
    have h2 : ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) x ≤
        ∑ t ∈ Finset.Icc 1 n, c t x + L * δ * n := by
      calc ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (c t) x
          ≤ ∑ t ∈ Finset.Icc 1 n, (c t x + L * δ) :=
            Finset.sum_le_sum fun t _ => by
              have := (abs_le.1 (hsm t x x.2)).2; linarith
        _ = ∑ t ∈ Finset.Icc 1 n, c t x + L * δ * n := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
              nsmul_eq_mul]
            ring
    linarith
  unfold pseudoRegret at hSM ⊢
  linarith
end BGDL3

open MeasureTheory BanditGD.Regret Pointwise in
theorem solution {d : ℕ} (hd : 1 ≤ d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (r R : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (hSR : S ⊆ Metric.closedBall 0 R)
    (C : ℝ) (hC : 0 < C) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hum : ∀ t, Measurable (u t))
    (hind : ProbabilityTheory.iIndepFun u P)
    (hlaw : ∀ t, P.map (u t) = RegretBandits.Nonlinear.uniformSphere d)
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (hn : 1 ≤ n) (ν δ α : ℝ) (hν : ν = R / (C * Real.sqrt n))
    (hδ : 0 < δ) (hδα : δ < α * r) (hα1 : α ≤ 1)
    (hrun : ∀ ω, IsBGDRun S α δ ν c (fun t => u t ω) (fun t => y t ω)) :
    RegretBandits.Nonlinear.pseudoRegret S c P (fun t ω => y t ω + δ • u t ω) n
      ≤ R * d * C * Real.sqrt n / δ + 3 * δ * (2 * C / (α * r)) * n + 2 * α * C * n := by
  exact BGDL3.eq10_main hd S hSconv hSclosed r R hr hrS hSR C hC c hcconv hcbdd P u hum hind hlaw
    y n hn ν δ α hν hδ hδα hα1 hrun
