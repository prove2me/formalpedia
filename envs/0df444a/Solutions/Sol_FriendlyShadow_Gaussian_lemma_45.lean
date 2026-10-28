-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_45
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T08:12:20.350049+00:00
-- url     : https://prove2.me/submissions/1fb17bf2-2b01-4eed-83a9-a89598d1ae14

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace E9Anal

lemma gauss_integral (d : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (-b * ‖v‖ ^ 2) = (Real.pi / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]; simp

lemma gauss_integrable (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : EuclideanSpace ℝ (Fin d) => Real.exp (-b * ‖v‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gauss_integral d hb]
  exact (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _).ne'

lemma vol_ball_le (d : ℕ) :
    volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) := by
  have hint := (gauss_integrable d (b := 1 / 2) (by norm_num)).const_mul (Real.exp (1 / 2))
  have h1 : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
      ∫ v : EuclideanSpace ℝ (Fin d), (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1).indicator 1 v := by
    rw [integral_indicator_one measurableSet_ball]
  rw [h1]
  calc _ ≤ ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (1 / 2) * Real.exp (-(1 / 2) * ‖v‖ ^ 2) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun v => Set.indicator_nonneg (fun _ _ => zero_le_one) v)
        · exact hint
        · refine Filter.Eventually.of_forall (fun v => ?_)
          by_cases hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1
          · show (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1).indicator 1 v ≤
              Real.exp (1 / 2) * Real.exp (-(1 / 2) * ‖v‖ ^ 2)
            rw [Set.indicator_of_mem hv, Pi.one_apply, ← Real.exp_add]
            rw [Metric.mem_ball, dist_zero_right] at hv
            have : ‖v‖ ^ 2 < 1 := by nlinarith [norm_nonneg v]
            exact Real.one_le_exp (by nlinarith)
          · rw [Set.indicator_of_notMem hv]; positivity
    _ = Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) := by
        rw [integral_const_mul, gauss_integral d (by norm_num)]
        congr 2; ring

lemma integral_exp_neg_norm (d : ℕ) :
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-‖y‖) =
      volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * (d.factorial : ℝ) := by
  have h := MeasureTheory.measure_unitBall_eq_integral_div_gamma
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (p := 1) one_pos
  simp only [Real.rpow_one, finrank_euclideanSpace, Fintype.card_fin, div_one] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  have hpos : 0 ≤ (∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-‖y‖)) / (d.factorial : ℝ) :=
    div_nonneg (integral_nonneg (fun _ => (Real.exp_pos _).le)) (by positivity)
  rw [measureReal_def, h, ENNReal.toReal_ofReal hpos]
  have : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma integral_exp_neg_mul_norm_le (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(c * ‖y‖)) ≤
      Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * (d.factorial : ℝ) / c ^ d := by
  have hs := MeasureTheory.Measure.integral_comp_smul
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (fun y => Real.exp (-‖y‖)) c
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, finrank_euclideanSpace,
    Fintype.card_fin, smul_eq_mul] at hs
  rw [hs, integral_exp_neg_norm, abs_of_pos (by positivity)]
  have hv := vol_ball_le d
  have hci : 0 < (c ^ d)⁻¹ := by positivity
  calc (c ^ d)⁻¹ * (volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * d.factorial)
      ≤ (c ^ d)⁻¹ * (Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * d.factorial) := by
        gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

lemma integral_exp_neg_mul_norm_eq (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(c * ‖y‖)) =
      (c ^ d)⁻¹ * (volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * (d.factorial : ℝ)) := by
  have hs := MeasureTheory.Measure.integral_comp_smul
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (fun y => Real.exp (-‖y‖)) c
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, finrank_euclideanSpace,
    Fintype.card_fin, smul_eq_mul] at hs
  rw [hs, integral_exp_neg_norm, abs_of_pos (by positivity)]

lemma integrable_exp_neg_mul_norm (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => Real.exp (-(c * ‖y‖))) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_neg_mul_norm_eq d hc]
  have hb : 0 < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have : (0:ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  positivity

end E9Anal

namespace E9Dens

open FriendlyShadow.Gaussian E9Anal

variable {d : ℕ}

lemma lgD_meas (abar : EuclideanSpace ℝ (Fin d)) (σ r : ℝ) : Measurable (lgDensity abar σ r) := by
  unfold lgDensity
  refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
  exact measurableSet_le (by fun_prop) measurable_const

lemma lgD_ge (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2)) ≤ lgDensity abar σ r x := by
  unfold lgDensity
  split_ifs with h
  · exact le_rfl
  · apply Real.exp_le_exp.mpr
    have key : -(‖x - abar‖ ^ 2) / (2 * σ ^ 2) - (-(‖x - abar‖ * r / σ) + r ^ 2 / 2) =
        -((‖x - abar‖ - r * σ) ^ 2) / (2 * σ ^ 2) := by
      field_simp; ring
    have : -((‖x - abar‖ - r * σ) ^ 2) / (2 * σ ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (‖x - abar‖ - r * σ)]) (by positivity)
    linarith

lemma lgD_nonneg (abar : EuclideanSpace ℝ (Fin d)) (σ r : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ lgDensity abar σ r x := by
  unfold lgDensity; split_ifs <;> exact (Real.exp_pos _).le

lemma lgD_le (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin d)) :
    lgDensity abar σ r x ≤ Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2)) +
      Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖)) := by
  unfold lgDensity
  have hp : 0 < Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖)) := by positivity
  split_ifs with h
  · linarith
  · have hgt : r * σ < ‖x - abar‖ := lt_of_not_ge h
    have h1 : Real.exp (-(‖x - abar‖ * r / σ) + r ^ 2 / 2) ≤
        Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : r ≤ ‖x - abar‖ / σ := by rw [le_div_iff₀ hσ]; linarith
      have e1 : ‖x - abar‖ * r / σ = r * (‖x - abar‖ / σ) := by ring
      have e2 : r / (8 * σ) * ‖x - abar‖ = r * (‖x - abar‖ / σ) / 8 := by field_simp
      rw [e1, e2]; nlinarith
    linarith [Real.exp_pos (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2))]

lemma gU_integrable (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2))) := by
  have h := (gauss_integrable d (b := 1 / (2 * σ ^ 2)) (by positivity)).comp_sub_right abar
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only; congr 1; field_simp

lemma sqrt_pow_eq (d : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (Real.pi / (1 / (2 * σ ^ 2))) ^ ((d : ℝ) / 2) = (Real.sqrt (2 * Real.pi) * σ) ^ d := by
  have ht : 0 ≤ Real.sqrt (2 * Real.pi) * σ := by positivity
  have : Real.pi / (1 / (2 * σ ^ 2)) = (Real.sqrt (2 * Real.pi) * σ) ^ (2:ℝ) := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (by positivity)]; field_simp
  rw [this, ← Real.rpow_mul ht, ← Real.rpow_natCast]; congr 1; ring

lemma gU_integral (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x : EuclideanSpace ℝ (Fin d), Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2)) =
      (Real.sqrt (2 * Real.pi) * σ) ^ d := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (fun x => Real.exp (-(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2)) abar
  rw [gauss_integral d (by positivity), sqrt_pow_eq d hσ] at h
  rw [← h]; congr 1; ext x; congr 1; field_simp

lemma tail_integrable (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖))) :=
  ((integrable_exp_neg_mul_norm d (c := r / (8 * σ)) (by positivity)).comp_sub_right abar).const_mul _

lemma lgD_integrable (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    Integrable (lgDensity abar σ r) := by
  refine Integrable.mono' ((gU_integrable abar hσ).add (tail_integrable abar hσ hr))
    (lgD_meas abar σ r).aestronglyMeasurable (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (lgD_nonneg abar σ r x)]
  exact lgD_le abar hσ hr x

lemma Z_ge (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    (Real.sqrt (2 * Real.pi) * σ) ^ d ≤ ∫ y, lgDensity abar σ r y := by
  rw [← gU_integral abar hσ]
  exact integral_mono (gU_integrable abar hσ) (lgD_integrable abar hσ hr) (fun x => lgD_ge abar hσ r x)

lemma Z_le (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    ∫ y, lgDensity abar σ r y ≤ (Real.sqrt (2 * Real.pi) * σ) ^ d +
      Real.exp (-(3 * r ^ 2 / 8)) *
        (Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * (d.factorial : ℝ) / (r / (8 * σ)) ^ d) := by
  calc ∫ y, lgDensity abar σ r y
      ≤ ∫ y, (Real.exp (-(‖y - abar‖ ^ 2) / (2 * σ ^ 2)) +
          Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖y - abar‖))) :=
        integral_mono (lgD_integrable abar hσ hr)
          ((gU_integrable abar hσ).add (tail_integrable abar hσ hr)) (fun x => lgD_le abar hσ hr x)
    _ = (Real.sqrt (2 * Real.pi) * σ) ^ d + Real.exp (-(3 * r ^ 2 / 8)) *
          ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (8 * σ) * ‖y‖)) := by
        rw [integral_add (gU_integrable abar hσ) (tail_integrable abar hσ hr), gU_integral abar hσ,
          integral_const_mul]
        congr 2
        exact integral_sub_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
          (fun y => Real.exp (-(r / (8 * σ) * ‖y‖))) abar
    _ ≤ _ := by
        gcongr
        exact integral_exp_neg_mul_norm_le d (by positivity)

/-- The excess factor `T = e^{-3r²/8} e^{1/2} d! (8/r)^d`. -/
noncomputable def T (d : ℕ) (r : ℝ) : ℝ :=
  Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (1 / 2) * (d.factorial : ℝ) * (8 / r) ^ d

lemma Z_le_T (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    ∫ y, lgDensity abar σ r y ≤ (1 + T d r) * (Real.sqrt (2 * Real.pi) * σ) ^ d := by
  refine (Z_le abar hσ hr).trans (le_of_eq ?_)
  have h2 : (2 * Real.pi) ^ ((d : ℝ) / 2) = Real.sqrt (2 * Real.pi) ^ d := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; ring
  rw [h2]; unfold T
  rw [div_pow, div_pow, mul_pow]
  field_simp
  ring

end E9Dens

namespace E9L45

open FriendlyShadow.Gaussian E9Anal E9Dens

variable {d : ℕ}

/-- The log-profile of the Laplace–Gaussian density in units of `σ`. -/
noncomputable def ng (r a : ℝ) : ℝ := if a ≤ r then -(a ^ 2) / 2 else -(a * r) + r ^ 2 / 2

lemma lgD_eq (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    lgDensity abar σ r x = Real.exp (ng r (‖x - abar‖ / σ)) := by
  unfold lgDensity ng
  have hiff : ‖x - abar‖ ≤ r * σ ↔ ‖x - abar‖ / σ ≤ r := by rw [div_le_iff₀ hσ]
  by_cases h : ‖x - abar‖ ≤ r * σ
  · rw [if_pos h, if_pos (hiff.mp h)]; congr 1; ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; congr 1; ring

lemma ng_lip {r a b δ : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : a - b ≤ δ)
    (h2 : b - a ≤ δ) : ng r a ≤ r * δ + ng r b := by
  have hδ : 0 ≤ δ := by linarith
  have k1 := mul_le_mul_of_nonneg_left h2 hr
  have k2 := mul_nonneg (sub_nonneg.2 h2) (add_nonneg ha hb)
  have k3 := mul_nonneg hr hδ
  unfold ng
  split_ifs with ha' hb' hb'
  · nlinarith
  · nlinarith [sq_nonneg (a - r)]
  · rw [not_le] at ha'
    nlinarith [mul_le_mul_of_nonneg_left ha'.le hr]
  · nlinarith

lemma ng_tail {r a : ℝ} (hr : 0 ≤ r) (ha : r ≤ a) : ng r a ≤ -(3 * r ^ 2 / 8) - r / 8 * a := by
  unfold ng
  split_ifs with h
  · have : a = r := le_antisymm h ha
    subst this; nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left ha hr]

lemma Z_pos (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    0 < ∫ y, lgDensity abar σ r y :=
  lt_of_lt_of_le (by positivity) (Z_ge abar hσ hr)

lemma isDensity_lg (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    IsDensity (lgPdf abar σ r) := by
  have hZ := Z_pos abar hσ hr
  refine ⟨fun x => div_nonneg (lgD_nonneg abar σ r x) hZ.le,
    (lgD_integrable abar hσ hr).div_const _, ?_⟩
  unfold lgPdf
  rw [integral_div, div_self hZ.ne']

lemma loglip (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    LogLipschitz (lgPdf abar σ r) (r / σ) := by
  have hZ := Z_pos abar hσ hr
  refine ⟨fun x => div_pos (by rw [lgD_eq abar hσ r x]; exact Real.exp_pos _) hZ, fun x y => ?_⟩
  unfold lgPdf
  rw [lgD_eq abar hσ r x, lgD_eq abar hσ r y, ← mul_div_assoc, ← Real.exp_add]
  apply (div_le_div_iff_of_pos_right hZ).mpr
  apply Real.exp_le_exp.mpr
  have hδ : r / σ * ‖x - y‖ = r * (‖x - y‖ / σ) := by ring
  rw [hδ]
  apply ng_lip hr.le (by positivity) (by positivity)
  · rw [← sub_div]; apply (div_le_div_iff_of_pos_right hσ).mpr
    calc ‖x - abar‖ - ‖y - abar‖ ≤ ‖(x - abar) - (y - abar)‖ := norm_sub_norm_le _ _
      _ = ‖x - y‖ := by congr 1; abel
  · rw [← sub_div]; apply (div_le_div_iff_of_pos_right hσ).mpr
    calc ‖y - abar‖ - ‖x - abar‖ ≤ ‖(y - abar) - (x - abar)‖ := norm_sub_norm_le _ _
      _ = ‖x - y‖ := by rw [norm_sub_rev]; congr 1; abel

lemma tail_pt (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 ≤ r)
    (x : EuclideanSpace ℝ (Fin d)) (hx : r * σ ≤ ‖x - abar‖) :
    lgDensity abar σ r x ≤ Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖)) := by
  rw [lgD_eq abar hσ r x, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ha : r ≤ ‖x - abar‖ / σ := by rw [le_div_iff₀ hσ]; exact hx
  have h := ng_tail hr ha
  have e : r / (8 * σ) * ‖x - abar‖ = r / 8 * (‖x - abar‖ / σ) := by ring
  rw [e]; linarith

lemma cB_eq (d : ℕ) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    Real.exp (-(3 * r ^ 2 / 8)) *
        (Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * (d.factorial : ℝ) / (r / (8 * σ)) ^ d) =
      T d r * (Real.sqrt (2 * Real.pi) * σ) ^ d := by
  have h2 : (2 * Real.pi) ^ ((d : ℝ) / 2) = Real.sqrt (2 * Real.pi) ^ d := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; ring
  rw [h2]; unfold T
  rw [div_pow, div_pow, mul_pow]
  field_simp
  ring

lemma cutoff_mass (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    densityMeasure (lgPdf abar σ r) {x | r * σ ≤ ‖x - abar‖} ≤ ENNReal.ofReal (T d r) := by
  have hZ := Z_pos abar hσ hr
  have hS : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | r * σ ≤ ‖x - abar‖} :=
    measurableSet_le measurable_const (by fun_prop)
  set Z := ∫ y, lgDensity abar σ r y with hZdef
  set c := Real.exp (-(3 * r ^ 2 / 8)) with hc
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => c * Real.exp (-(r / (8 * σ) * ‖x - abar‖)) / Z
  have hg_int : Integrable g := (tail_integrable abar hσ hr).div_const _
  have hg_nn : ∀ x, 0 ≤ g x := fun x => by positivity
  unfold densityMeasure
  rw [withDensity_apply _ hS]
  calc ∫⁻ x in {x | r * σ ≤ ‖x - abar‖}, ENNReal.ofReal (lgPdf abar σ r x)
      ≤ ∫⁻ x in {x | r * σ ≤ ‖x - abar‖}, ENNReal.ofReal (g x) := by
        apply setLIntegral_mono' hS
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        unfold lgPdf
        exact (div_le_div_iff_of_pos_right hZ).mpr (tail_pt abar hσ hr.le x hx)
    _ ≤ ∫⁻ x, ENNReal.ofReal (g x) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x, g x) :=
        (ofReal_integral_eq_lintegral_ofReal hg_int (Filter.Eventually.of_forall hg_nn)).symm
    _ ≤ ENNReal.ofReal (T d r) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : ∫ x, g x =
            c * (∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (8 * σ) * ‖y‖))) / Z := by
          simp only [g]; rw [integral_div, integral_const_mul]
          congr 2
          exact integral_sub_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
            (fun y => Real.exp (-(r / (8 * σ) * ‖y‖))) abar
        rw [h1]
        have hI := integral_exp_neg_mul_norm_le d (c := r / (8 * σ)) (by positivity)
        have hI0 : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (8 * σ) * ‖y‖)) :=
          integral_nonneg (fun _ => (Real.exp_pos _).le)
        have hZg := Z_ge abar hσ hr
        have hZg0 : 0 < (Real.sqrt (2 * Real.pi) * σ) ^ d := by positivity
        have hc0 : 0 ≤ c := (Real.exp_pos _).le
        calc c * (∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (8 * σ) * ‖y‖))) / Z
            ≤ c * (∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (8 * σ) * ‖y‖))) /
                (Real.sqrt (2 * Real.pi) * σ) ^ d :=
              div_le_div_of_nonneg_left (mul_nonneg hc0 hI0) hZg0 hZg
          _ ≤ c * (Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * (d.factorial : ℝ) /
                (r / (8 * σ)) ^ d) / (Real.sqrt (2 * Real.pi) * σ) ^ d := by gcongr
          _ = T d r := by rw [hc, cB_eq d hσ hr]; field_simp

lemma T_bound {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) :
    T d (4 * Real.sqrt (d * Real.log n)) * ((d : ℝ) * (n.choose d : ℝ)) ≤ 1 := by
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hd.trans hdn
  have hnpos : (0:ℝ) < n := by linarith
  have hL : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]; linarith [Real.exp_one_lt_d9]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hdL : 1 ≤ (d:ℝ) * Real.log n := by nlinarith
  set r := 4 * Real.sqrt (d * Real.log n) with hr
  have hsq : Real.sqrt (d * Real.log n) ^ 2 = d * Real.log n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt (d * Real.log n) := by rw [Real.one_le_sqrt]; linarith
  have hr4 : 4 ≤ r := by rw [hr]; linarith
  have hexp : Real.exp (-(3 * r ^ 2 / 8)) * (n:ℝ) ^ (6 * d) = 1 := by
    have e : 3 * r ^ 2 / 8 = ((6 * d : ℕ) : ℝ) * Real.log n := by
      rw [hr, mul_pow, hsq]; push_cast; ring
    rw [e, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnpos]
    exact inv_mul_cancel₀ (by positivity)
  have hdesc : (d.factorial : ℝ) * (n.choose d : ℝ) ≤ (n:ℝ) ^ d := by
    have h := Nat.descFactorial_le_pow n d
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast h
  have h8 : (8 / r) ^ d ≤ (n:ℝ) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have he : Real.exp (1 / 2) ≤ 3 := by
    linarith [Real.exp_one_lt_d9, Real.exp_le_exp.mpr (by norm_num : (1:ℝ) / 2 ≤ 1)]
  have hdn' : (d:ℝ) ≤ n := by exact_mod_cast hdn
  have hpow : (n:ℝ) ^ (2 * d + 2) ≤ (n:ℝ) ^ (6 * d) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hE0 : 0 ≤ Real.exp (-(3 * r ^ 2 / 8)) := (Real.exp_pos _).le
  unfold T
  calc Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (1 / 2) * (d.factorial : ℝ) * (8 / r) ^ d *
        ((d : ℝ) * (n.choose d : ℝ))
      = Real.exp (-(3 * r ^ 2 / 8)) * (Real.exp (1 / 2) * (8 / r) ^ d * (d : ℝ) *
          ((d.factorial : ℝ) * (n.choose d : ℝ))) := by ring
    _ ≤ Real.exp (-(3 * r ^ 2 / 8)) * (3 * (n:ℝ) ^ d * n * (n:ℝ) ^ d) := by gcongr
    _ ≤ Real.exp (-(3 * r ^ 2 / 8)) * (n:ℝ) ^ (6 * d) := by
        gcongr
        calc 3 * (n:ℝ) ^ d * n * (n:ℝ) ^ d ≤ n * (n:ℝ) ^ d * n * (n:ℝ) ^ d := by gcongr
          _ = (n:ℝ) ^ (2 * d + 2) := by ring
          _ ≤ (n:ℝ) ^ (6 * d) := hpow
    _ = 1 := hexp

lemma ng_mono {r a0 a : ℝ} (hr : 0 ≤ r) (ha0 : 0 ≤ a0) (h : a0 ≤ a) : ng r a ≤ ng r a0 := by
  unfold ng; split_ifs with h1 h2 h2 <;> nlinarith

lemma ng_line {r a0 a t : ℝ} (hr : 0 ≤ r) (ha0 : 0 ≤ a0) (ha : 0 ≤ a)
    (h : a ^ 2 = a0 ^ 2 + t ^ 2) : ng r a0 - t ^ 2 / 2 ≤ ng r a := by
  have haa : a0 ≤ a := by nlinarith [sq_nonneg t]
  have hsub := sub_nonneg.2 haa
  unfold ng; split_ifs with h1 h2 h2 <;> nlinarith [sq_nonneg (a - r)]

lemma final_arith {σ M0 X H s : ℝ} (hσ : 0 < σ) (hM0 : 0 < M0) (hs : s = σ / 2)
    (hI : s ^ 2 * M0 - s ^ 2 * H * (2 * s) ≤ X) (hlow : 2 * σ * H ≤ M0) :
    (σ / 4) ^ 2 * M0 ^ 2 ≤ M0 * X := by
  subst hs
  nlinarith [mul_le_mul_of_nonneg_left hI hM0.le,
    mul_le_mul_of_nonneg_left hlow (mul_nonneg (sq_nonneg σ) hM0.le),
    mul_nonneg (sq_nonneg σ) (sq_nonneg M0)]

set_option maxHeartbeats 1000000 in
lemma linevar (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    LineVarianceGE (lgPdf abar σ r) (σ / 4) := by
  intro v w hw hI0 hI2 hM0
  set μ := lgPdf abar σ r with hμ
  have hZ := Z_pos abar hσ hr
  set γ0 : ℝ := -⟪v - abar, w⟫ with hγ0
  have geo : ∀ γ : ℝ, ‖v + γ • w - abar‖ ^ 2 = ‖v + γ0 • w - abar‖ ^ 2 + (γ - γ0) ^ 2 := by
    intro γ
    have e : ∀ c : ℝ, v + c • w - abar = (v - abar) + c • w := fun c => by abel
    rw [e, e, norm_add_sq_real, norm_add_sq_real, inner_smul_right, inner_smul_right, norm_smul,
      norm_smul, hw, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, sq_abs, sq_abs, hγ0]
    ring
  have hpt : ∀ γ : ℝ, μ (v + γ • w) =
      Real.exp (ng r (‖v + γ • w - abar‖ / σ)) / ∫ y, lgDensity abar σ r y := by
    intro γ; rw [hμ]; unfold lgPdf; rw [lgD_eq abar hσ r]
  have hμnn : ∀ γ : ℝ, 0 ≤ μ (v + γ • w) := fun γ => by rw [hpt]; positivity
  set H := μ (v + γ0 • w) with hH
  have hup : ∀ γ : ℝ, μ (v + γ • w) ≤ H := by
    intro γ
    rw [hH, hpt, hpt]
    apply (div_le_div_iff_of_pos_right hZ).mpr
    apply Real.exp_le_exp.mpr
    apply ng_mono hr.le (by positivity)
    apply (div_le_div_iff_of_pos_right hσ).mpr
    have := geo γ
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [sq_nonneg (γ - γ0)])
  have hlow : ∀ γ : ℝ, H * Real.exp (-(1 / (2 * σ ^ 2)) * (γ - γ0) ^ 2) ≤ μ (v + γ • w) := by
    intro γ
    rw [hH, hpt, hpt, div_mul_eq_mul_div, ← Real.exp_add]
    apply (div_le_div_iff_of_pos_right hZ).mpr
    apply Real.exp_le_exp.mpr
    have h := ng_line (r := r) (t := (γ - γ0) / σ) hr.le
      (by positivity : 0 ≤ ‖v + γ0 • w - abar‖ / σ)
      (by positivity : 0 ≤ ‖v + γ • w - abar‖ / σ) (by rw [div_pow, div_pow, div_pow, geo γ]; ring)
    have e : -(1 / (2 * σ ^ 2)) * (γ - γ0) ^ 2 = -(((γ - γ0) / σ) ^ 2 / 2) := by ring
    linarith
  have hH0 : 0 ≤ H := hμnn γ0
  set M0 := ∫ γ : ℝ, μ (v + γ • w) with hM0def
  set M1 := ∫ γ : ℝ, γ * μ (v + γ • w) with hM1def
  set M2 := ∫ γ : ℝ, γ ^ 2 * μ (v + γ • w) with hM2def
  -- lower bound on the mass
  have hgi : Integrable (fun γ : ℝ => H * Real.exp (-(1 / (2 * σ ^ 2)) * (γ - γ0) ^ 2)) :=
    ((integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < 1 / (2 * σ ^ 2))).comp_sub_right γ0).const_mul H
  have hgauss : ∫ γ : ℝ, H * Real.exp (-(1 / (2 * σ ^ 2)) * (γ - γ0) ^ 2) =
      H * Real.sqrt (Real.pi / (1 / (2 * σ ^ 2))) := by
    rw [integral_const_mul]; congr 1
    rw [integral_sub_right_eq_self (fun γ => Real.exp (-(1 / (2 * σ ^ 2)) * γ ^ 2)) γ0]
    exact integral_gaussian _
  have hsq : 2 * σ ≤ Real.sqrt (Real.pi / (1 / (2 * σ ^ 2))) := by
    calc 2 * σ = Real.sqrt ((2 * σ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.pi / (1 / (2 * σ ^ 2))) := by
          apply Real.sqrt_le_sqrt
          rw [div_div_eq_mul_div, div_one]; nlinarith [Real.pi_gt_three, sq_nonneg σ]
  have hM0low : 2 * σ * H ≤ M0 := by
    calc 2 * σ * H ≤ H * Real.sqrt (Real.pi / (1 / (2 * σ ^ 2))) := by nlinarith
      _ = _ := hgauss.symm
      _ ≤ M0 := integral_mono hgi hI0 hlow
  -- first moment integrability
  have hmμ : Measurable μ := by rw [hμ]; unfold lgPdf; exact (lgD_meas abar σ r).div_const _
  have hmeas : Measurable (fun γ : ℝ => μ (v + γ • w)) := hmμ.comp (by fun_prop)
  have hI1 : Integrable (fun γ : ℝ => γ * μ (v + γ • w)) := by
    refine Integrable.mono' (hI0.add hI2) (measurable_id.mul hmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun γ => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμnn γ)]
    have h1 : |γ| ≤ 1 + γ ^ 2 := by
      rcases abs_cases γ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [sq_nonneg (γ - 1), sq_nonneg (γ + 1)]
    have := mul_le_mul_of_nonneg_right h1 (hμnn γ)
    simp only [Pi.add_apply]; linarith
  -- variance identity
  set m := M1 / M0 with hm
  have hmM : m * M0 = M1 := div_mul_cancel₀ M1 hM0.ne'
  have hfun : (fun γ : ℝ => (γ - m) ^ 2 * μ (v + γ • w)) =
      fun γ => (γ ^ 2 * μ (v + γ • w) - (2 * m) * (γ * μ (v + γ • w))) + m ^ 2 * μ (v + γ • w) := by
    ext γ; ring
  have hexp : ∫ γ : ℝ, (γ - m) ^ 2 * μ (v + γ • w) = M2 - 2 * m * M1 + m ^ 2 * M0 := by
    have hA : Integrable (fun γ : ℝ => γ ^ 2 * μ (v + γ • w) - (2 * m) * (γ * μ (v + γ • w))) :=
      hI2.sub (hI1.const_mul _)
    rw [hfun, integral_add hA (hI0.const_mul _),
      integral_sub hI2 (hI1.const_mul _), integral_const_mul, integral_const_mul]
  have hVint : Integrable (fun γ : ℝ => (γ - m) ^ 2 * μ (v + γ • w)) := by
    rw [hfun]; exact (hI2.sub (hI1.const_mul _)).add (hI0.const_mul _)
  -- Chebyshev-type lower bound with s = σ/2
  set s := σ / 2 with hs
  have hs0 : 0 < s := by positivity
  set ind : ℝ → ℝ := (Set.Icc (m - s) (m + s)).indicator 1 with hind
  have hindI : Integrable ind :=
    (integrableOn_const (measure_Icc_lt_top (a := m - s) (b := m + s)).ne).integrable_indicator
      measurableSet_Icc
  have hindV : ∫ γ, ind γ = 2 * s := by
    rw [hind, integral_indicator_one measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hptw : ∀ γ : ℝ, s ^ 2 * μ (v + γ • w) - s ^ 2 * H * ind γ ≤ (γ - m) ^ 2 * μ (v + γ • w) := by
    intro γ
    by_cases hγ : γ ∈ Set.Icc (m - s) (m + s)
    · rw [hind, Set.indicator_of_mem hγ, Pi.one_apply, mul_one]
      nlinarith [mul_nonneg (sq_nonneg (γ - m)) (hμnn γ),
        mul_le_mul_of_nonneg_left (hup γ) (sq_nonneg s)]
    · rw [hind, Set.indicator_of_notMem hγ, mul_zero, sub_zero]
      have hfar : s ^ 2 ≤ (γ - m) ^ 2 := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hγ
        rcases hγ with h | h <;> nlinarith
      exact mul_le_mul_of_nonneg_right hfar (hμnn γ)
  have hI : s ^ 2 * M0 - s ^ 2 * H * (2 * s) ≤ M2 - 2 * m * M1 + m ^ 2 * M0 := by
    rw [← hexp, ← hindV, ← integral_const_mul, ← integral_const_mul (s ^ 2 * H),
      ← integral_sub (hI0.const_mul _) (hindI.const_mul _)]
    exact integral_mono ((hI0.const_mul _).sub (hindI.const_mul _)) hVint hptw
  have key : M2 * M0 - M1 ^ 2 = M0 * (M2 - 2 * m * M1 + m ^ 2 * M0) := by
    rw [← hmM]; ring
  rw [key]
  exact final_arith hσ hM0 hs hI hM0low

lemma ng_glob (r a : ℝ) : ng r a ≤ -(a * r) + r ^ 2 / 2 := by
  unfold ng; split_ifs with h
  · nlinarith [sq_nonneg (a - r)]
  · exact le_rfl

lemma lgD_glob (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    lgDensity abar σ r x ≤ Real.exp (r ^ 2 / 2) * Real.exp (-(r / σ * ‖x - abar‖)) := by
  rw [lgD_eq abar hσ r x, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := ng_glob r (‖x - abar‖ / σ)
  have e : r ^ 2 / 2 + -(r / σ * ‖x - abar‖) = -(‖x - abar‖ / σ * r) + r ^ 2 / 2 := by ring
  rw [e]; exact h

lemma norm_mul_exp_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    t * Real.exp (-(c * t)) ≤ 2 / c * Real.exp (-(c / 2 * t)) := by
  have h1 : c / 2 * t ≤ Real.exp (c / 2 * t) := by linarith [Real.add_one_le_exp (c / 2 * t)]
  have h2 : Real.exp (-(c * t)) = Real.exp (-(c / 2 * t)) * Real.exp (-(c / 2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (c / 2 * t) * Real.exp (-(c / 2 * t)) = 1 := by
    rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-(c / 2 * t))
  rw [h2]
  calc t * (Real.exp (-(c / 2 * t)) * Real.exp (-(c / 2 * t)))
      = 2 / c * ((c / 2 * t) * Real.exp (-(c / 2 * t))) * Real.exp (-(c / 2 * t)) := by
        field_simp
    _ ≤ 2 / c * (Real.exp (c / 2 * t) * Real.exp (-(c / 2 * t))) * Real.exp (-(c / 2 * t)) := by
        gcongr
    _ = 2 / c * Real.exp (-(c / 2 * t)) := by rw [h3, mul_one]

lemma hasMean_lg (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    HasMean (lgPdf abar σ r) abar := by
  set μ := lgPdf abar σ r with hμ
  have hZ := Z_pos abar hσ hr
  set Z := ∫ y, lgDensity abar σ r y with hZdef
  have hmμ : Measurable μ := by rw [hμ]; unfold lgPdf; exact (lgD_meas abar σ r).div_const _
  have hμnn : ∀ x, 0 ≤ μ x := fun x => div_nonneg (lgD_nonneg abar σ r x) hZ.le
  have hμint : Integrable μ := (lgD_integrable abar hσ hr).div_const _
  set c := r / σ with hc
  have hc0 : 0 < c := by positivity
  set K := Real.exp (r ^ 2 / 2) / Z with hK
  have hμle : ∀ x, μ x ≤ K * Real.exp (-(c * ‖x - abar‖)) := by
    intro x; rw [hμ, hK]; unfold lgPdf
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hZ).mpr (lgD_glob abar hσ r x)
  have hb1 : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      K * (2 / c * Real.exp (-(c / 2 * ‖x - abar‖)))) :=
    (((integrable_exp_neg_mul_norm d (by positivity : 0 < c / 2)).comp_sub_right abar).const_mul _).const_mul _
  have hb2 : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      K * Real.exp (-(c * ‖x - abar‖)) * ‖abar‖) :=
    (((integrable_exp_neg_mul_norm d hc0).comp_sub_right abar).const_mul _).mul_const _
  have hint : Integrable (fun x => μ x • x) := by
    refine Integrable.mono' (hb1.add hb2) (hmμ.smul measurable_id).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hμnn x)]
    have hx : ‖x‖ ≤ ‖x - abar‖ + ‖abar‖ := by
      calc ‖x‖ = ‖(x - abar) + abar‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hK0 : 0 ≤ K := by positivity
    have h1 := mul_le_mul_of_nonneg_left (norm_mul_exp_le hc0 (norm_nonneg (x - abar))) hK0
    have h2 := mul_le_mul_of_nonneg_left hx (hμnn x)
    have h3 := mul_le_mul_of_nonneg_right (hμle x) (norm_nonneg (x - abar))
    have h4 := mul_le_mul_of_nonneg_right (hμle x) (norm_nonneg abar)
    simp only [Pi.add_apply]
    nlinarith
  refine ⟨hint, ?_⟩
  have hconst : Integrable (fun x => μ x • abar) := hμint.smul_const abar
  have hsplit : (fun x => μ x • x) = fun x => μ x • (x - abar) + μ x • abar := by
    ext x; rw [← smul_add, sub_add_cancel]
  have hint2 : Integrable (fun x => μ x • (x - abar)) := by
    have := hint.sub hconst
    refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp [smul_sub]
  have hsym : ∀ y, μ (-y + abar) = μ (y + abar) := by
    intro y; rw [hμ]; unfold lgPdf lgDensity; simp [norm_neg]
  have hzero : ∫ x, μ x • (x - abar) = 0 := by
    have hs : ∫ x, μ x • (x - abar) = ∫ y, μ (y + abar) • y := by
      rw [← integral_add_right_eq_self (fun x => μ x • (x - abar)) abar]
      simp only [add_sub_cancel_right]
    rw [hs]
    have hn := integral_neg_eq_self (fun y => μ (y + abar) • y)
      (volume : Measure (EuclideanSpace ℝ (Fin d)))
    simp only [hsym, smul_neg, integral_neg] at hn
    set I := ∫ y, μ (y + abar) • y with hI
    have h : I = -I := hn.symm
    calc I = (1 / 2 : ℝ) • (I + I) := by rw [← two_smul ℝ I, smul_smul]; norm_num
      _ = (1 / 2 : ℝ) • (I + -I) := by rw [← h]
      _ = 0 := by rw [add_neg_cancel, smul_zero]
  rw [hsplit, integral_add hint2 hconst, hzero, zero_add, integral_smul_const]
  have h1 : ∫ x, μ x = 1 := (isDensity_lg abar hσ hr).2.2
  rw [h1, one_smul]

noncomputable def T16 (d : ℕ) (r : ℝ) : ℝ :=
  Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (1 / 2) * (d.factorial : ℝ) * (16 / r) ^ d

lemma cB16_eq (d : ℕ) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    Real.exp (-(3 * r ^ 2 / 8)) *
        (Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * (d.factorial : ℝ) / (r / (16 * σ)) ^ d) =
      T16 d r * (Real.sqrt (2 * Real.pi) * σ) ^ d := by
  have h2 : (2 * Real.pi) ^ ((d : ℝ) / 2) = Real.sqrt (2 * Real.pi) ^ d := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; ring
  rw [h2]; unfold T16
  rw [div_pow, div_pow, mul_pow]
  field_simp
  ring

lemma T16_bound {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) :
    T16 d (4 * Real.sqrt (d * Real.log n)) * (4 * (n : ℝ)) ≤ 1 := by
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hd.trans hdn
  have hnpos : (0:ℝ) < n := by linarith
  have hL : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]; linarith [Real.exp_one_lt_d9]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hdL : 1 ≤ (d:ℝ) * Real.log n := by nlinarith
  set r := 4 * Real.sqrt (d * Real.log n) with hr
  have hsq : Real.sqrt (d * Real.log n) ^ 2 = d * Real.log n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt (d * Real.log n) := by rw [Real.one_le_sqrt]; linarith
  have hr4 : 4 ≤ r := by rw [hr]; linarith
  have hexp : Real.exp (-(3 * r ^ 2 / 8)) * (n:ℝ) ^ (6 * d) = 1 := by
    have e : 3 * r ^ 2 / 8 = ((6 * d : ℕ) : ℝ) * Real.log n := by
      rw [hr, mul_pow, hsq]; push_cast; ring
    rw [e, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnpos]
    exact inv_mul_cancel₀ (by positivity)
  have hfac : (d.factorial : ℝ) ≤ (n:ℝ) ^ d := by
    have h := Nat.descFactorial_le_pow n d
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    have hc := Nat.choose_pos hdn
    have : d.factorial ≤ d.factorial * n.choose d := Nat.le_mul_of_pos_right _ hc
    exact_mod_cast this.trans h
  have h16 : (16 / r) ^ d ≤ (n:ℝ) ^ (2 * d) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have he : Real.exp (1 / 2) ≤ 3 := by
    linarith [Real.exp_one_lt_d9, Real.exp_le_exp.mpr (by norm_num : (1:ℝ) / 2 ≤ 1)]
  have hpow : (n:ℝ) ^ (3 * d + 4) ≤ (n:ℝ) ^ (6 * d) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have h12 : (12:ℝ) ≤ (n:ℝ) ^ 3 :=
    calc (12:ℝ) ≤ 3 ^ 3 := by norm_num
      _ ≤ (n:ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn3 3
  unfold T16
  calc Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (1 / 2) * (d.factorial : ℝ) * (16 / r) ^ d *
        (4 * (n : ℝ))
      = Real.exp (-(3 * r ^ 2 / 8)) * (Real.exp (1 / 2) * (16 / r) ^ d * (d.factorial : ℝ) *
          (4 * (n : ℝ))) := by ring
    _ ≤ Real.exp (-(3 * r ^ 2 / 8)) * (3 * (n:ℝ) ^ (2 * d) * (n:ℝ) ^ d * (4 * (n : ℝ))) := by
        gcongr
    _ ≤ Real.exp (-(3 * r ^ 2 / 8)) * (n:ℝ) ^ (6 * d) := by
        gcongr
        calc 3 * (n:ℝ) ^ (2 * d) * (n:ℝ) ^ d * (4 * (n : ℝ)) = 12 * (n:ℝ) ^ (3 * d + 1) := by ring
          _ ≤ (n:ℝ) ^ 3 * (n:ℝ) ^ (3 * d + 1) := by gcongr
          _ = (n:ℝ) ^ (3 * d + 4) := by ring
          _ ≤ (n:ℝ) ^ (6 * d) := hpow
    _ = 1 := hexp

lemma mgf_pt {σ : ℝ} (hσ : 0 < σ) (lam : ℝ) (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ = 1)
    (y : EuclideanSpace ℝ (Fin d)) :
    Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, θ⟫) =
      Real.exp (lam ^ 2 * σ ^ 2 / 2) * Real.exp (-(‖y - (lam * σ ^ 2) • θ‖ ^ 2) / (2 * σ ^ 2)) := by
  rw [← Real.exp_add, ← Real.exp_add]; congr 1
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, hθ, Real.norm_eq_abs, mul_one, sq_abs]
  field_simp; ring

lemma mgf_int (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (lam : ℝ) (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ = 1) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
        Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, θ⟫)) ∧
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, θ⟫) =
      (Real.sqrt (2 * Real.pi) * σ) ^ d * Real.exp (lam ^ 2 * σ ^ 2 / 2) := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, θ⟫)) =
      fun y => Real.exp (lam ^ 2 * σ ^ 2 / 2) *
        Real.exp (-(‖y - (lam * σ ^ 2) • θ‖ ^ 2) / (2 * σ ^ 2)) :=
    funext (mgf_pt hσ lam θ hθ)
  rw [hfun]
  exact ⟨(gU_integrable _ hσ).const_mul _, by rw [integral_const_mul, gU_integral _ hσ]; ring⟩

lemma pt_bound (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ = 1) {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : t ≤ |⟪x - abar, θ⟫|) :
    lgDensity abar σ r x ≤
      Real.exp ((-lam) * t) * (Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2)) *
          Real.exp (lam * ⟪x - abar, θ⟫) +
        Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪x - abar, -θ⟫)) +
      Real.exp ((-(r / (16 * σ))) * t) *
        (Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (16 * σ) * ‖x - abar‖))) := by
  have h0 := lgD_le abar hσ hr x
  rw [inner_neg_right]
  have hsρ : |⟪x - abar, θ⟫| ≤ ‖x - abar‖ := by
    have := abs_real_inner_le_norm (x - abar) θ; rwa [hθ, mul_one] at this
  set s := ⟪x - abar, θ⟫ with hs
  set ρ := ‖x - abar‖ with hρ
  set G := Real.exp (-(ρ ^ 2) / (2 * σ ^ 2)) with hG
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hE : 1 ≤ Real.exp ((-lam) * t) * (Real.exp (lam * s) + Real.exp (lam * -s)) := by
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
    · calc (1:ℝ) ≤ Real.exp ((-lam) * t + lam * s) :=
            Real.one_le_exp (by nlinarith [mul_nonneg hlam (show (0:ℝ) ≤ |s| - t by linarith)])
        _ = Real.exp ((-lam) * t) * Real.exp (lam * s) := Real.exp_add _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_pos _).le)
            (Real.exp_pos _).le
    · calc (1:ℝ) ≤ Real.exp ((-lam) * t + lam * -s) :=
            Real.one_le_exp (by nlinarith [mul_nonneg hlam (show (0:ℝ) ≤ |s| - t by linarith)])
        _ = Real.exp ((-lam) * t) * Real.exp (lam * -s) := Real.exp_add _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_pos _).le)
            (Real.exp_pos _).le
  have h1 : G ≤ Real.exp ((-lam) * t) * (G * Real.exp (lam * s) + G * Real.exp (lam * -s)) := by
    have := mul_le_mul_of_nonneg_left hE hG0
    calc G = G * 1 := (mul_one G).symm
      _ ≤ _ := this
      _ = _ := by ring
  have h2 : Real.exp (-(r / (8 * σ) * ρ)) ≤
      Real.exp ((-(r / (16 * σ))) * t) * Real.exp (-(r / (16 * σ) * ρ)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have ha0 : 0 ≤ r / (16 * σ) := by positivity
    have e : r / (8 * σ) = 2 * (r / (16 * σ)) := by field_simp; ring
    rw [e]
    have : t ≤ ρ := hx.trans hsρ
    nlinarith [mul_le_mul_of_nonneg_left this ha0]
  have hc0 : 0 ≤ Real.exp (-(3 * r ^ 2 / 8)) := (Real.exp_pos _).le
  have h3 := mul_le_mul_of_nonneg_left h2 hc0
  calc lgDensity abar σ r x ≤ G + Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ρ)) := h0
    _ ≤ _ := by nlinarith [h1, h3]

lemma tail_t (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ = 1) {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    densityMeasure (lgPdf abar σ r) {x | t ≤ |⟪x - abar, θ⟫|} ≤
      ENNReal.ofReal (Real.exp ((-lam) * t) *
          (2 * (Real.sqrt (2 * Real.pi) * σ) ^ d * Real.exp (lam ^ 2 * σ ^ 2 / 2) /
            ∫ y, lgDensity abar σ r y) +
        Real.exp ((-(r / (16 * σ))) * t) *
          (Real.exp (-(3 * r ^ 2 / 8)) *
            (∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (16 * σ) * ‖y‖))) /
            ∫ y, lgDensity abar σ r y)) := by
  have hZ := Z_pos abar hσ hr
  have hθ' : ‖-θ‖ = 1 := by rw [norm_neg, hθ]
  have hf1 := (mgf_int d hσ lam θ hθ).1
  have hf2 := (mgf_int d hσ lam (-θ) hθ').1
  have hf3 : Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (16 * σ) * ‖y‖))) :=
    (integrable_exp_neg_mul_norm d (by positivity)).const_mul _
  have hf12 : Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, θ⟫) +
        Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, -θ⟫)) := hf1.add hf2
  have hA : Integrable (fun y : EuclideanSpace ℝ (Fin d) => Real.exp ((-lam) * t) *
      (Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, θ⟫) +
        Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, -θ⟫))) := hf12.const_mul _
  have hB : Integrable (fun y : EuclideanSpace ℝ (Fin d) => Real.exp ((-(r / (16 * σ))) * t) *
      (Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (16 * σ) * ‖y‖)))) := hf3.const_mul _
  set B : EuclideanSpace ℝ (Fin d) → ℝ := fun y => Real.exp ((-lam) * t) *
      (Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, θ⟫) +
        Real.exp (-(‖y‖ ^ 2) / (2 * σ ^ 2)) * Real.exp (lam * ⟪y, -θ⟫)) +
      Real.exp ((-(r / (16 * σ))) * t) *
        (Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (16 * σ) * ‖y‖))) with hBdef
  have hBint : Integrable B := hA.add hB
  have hBval : ∫ y, B y = Real.exp ((-lam) * t) *
        (2 * (Real.sqrt (2 * Real.pi) * σ) ^ d * Real.exp (lam ^ 2 * σ ^ 2 / 2)) +
      Real.exp ((-(r / (16 * σ))) * t) * (Real.exp (-(3 * r ^ 2 / 8)) *
        ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (16 * σ) * ‖y‖))) := by
    rw [hBdef, integral_add hA hB, integral_const_mul, integral_const_mul,
      integral_add hf1 hf2, (mgf_int d hσ lam θ hθ).2, (mgf_int d hσ lam (-θ) hθ').2,
      integral_const_mul]
    ring
  have hS : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | t ≤ |⟪x - abar, θ⟫|} :=
    measurableSet_le measurable_const
      (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => |⟪x - abar, θ⟫|).measurable
  set Z := ∫ y, lgDensity abar σ r y with hZdef
  have hg_int : Integrable (fun x => B (x - abar) / Z) := (hBint.comp_sub_right abar).div_const _
  have hBnn : ∀ y, 0 ≤ B y := fun y => by rw [hBdef]; positivity
  unfold densityMeasure
  rw [withDensity_apply _ hS]
  calc ∫⁻ x in {x | t ≤ |⟪x - abar, θ⟫|}, ENNReal.ofReal (lgPdf abar σ r x)
      ≤ ∫⁻ x in {x | t ≤ |⟪x - abar, θ⟫|}, ENNReal.ofReal (B (x - abar) / Z) := by
        apply setLIntegral_mono' hS
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        unfold lgPdf
        apply (div_le_div_iff_of_pos_right hZ).mpr
        rw [hBdef]
        exact pt_bound abar hσ hr θ hθ hlam t x hx
    _ ≤ ∫⁻ x, ENNReal.ofReal (B (x - abar) / Z) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x, B (x - abar) / Z) :=
        (ofReal_integral_eq_lintegral_ofReal hg_int
          (Filter.Eventually.of_forall (fun x => div_nonneg (hBnn _) hZ.le))).symm
    _ = _ := by
        congr 1
        rw [integral_div, integral_sub_right_eq_self (fun y => B y) abar, hBval]
        ring

set_option maxHeartbeats 1000000 in
lemma nthdev_lg {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ}
    (hσ : 0 < σ) :
    NthDeviationLE (lgPdf abar σ (4 * Real.sqrt (d * Real.log n))) abar n
      (4 * σ * Real.sqrt (Real.log n)) := by
  intro θ hθ
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hd.trans hdn
  have hnpos : (0:ℝ) < n := by linarith
  have hL : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]; linarith [Real.exp_one_lt_d9]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hsL : 1 ≤ Real.sqrt (Real.log n) := by rw [Real.one_le_sqrt]; exact hL
  have hsdL : 1 ≤ Real.sqrt (d * Real.log n) := by rw [Real.one_le_sqrt]; nlinarith
  set r := 4 * Real.sqrt (d * Real.log n) with hr
  set R := 4 * σ * Real.sqrt (Real.log n) with hR
  have hr4 : 4 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hR4 : 4 * σ ≤ R := by rw [hR]; nlinarith
  have hR0 : 0 < R := by linarith
  have hR2 : R ^ 2 = 16 * σ ^ 2 * Real.log n := by
    rw [hR, mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
  set lam := R / σ ^ 2 with hlam
  have hlam0 : 0 < lam := by positivity
  have ha0 : 0 < r / (16 * σ) := by positivity
  have hZ := Z_pos abar hσ hr0
  have hZg := Z_ge abar hσ hr0
  have hZg0 : 0 < (Real.sqrt (2 * Real.pi) * σ) ^ d := by positivity
  set Z := ∫ y, lgDensity abar σ r y with hZdef
  set P := 2 * (Real.sqrt (2 * Real.pi) * σ) ^ d * Real.exp (lam ^ 2 * σ ^ 2 / 2) / Z with hP
  set I := ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (16 * σ) * ‖y‖)) with hIdef
  have hI0 : 0 ≤ I := integral_nonneg (fun _ => (Real.exp_pos _).le)
  set Q := Real.exp (-(3 * r ^ 2 / 8)) * I / Z with hQ
  have hc0 : 0 ≤ Real.exp (-(3 * r ^ 2 / 8)) := (Real.exp_pos _).le
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hQ0 : 0 ≤ Q := div_nonneg (mul_nonneg hc0 hI0) hZ.le
  have hi1 := (integrableOn_exp_mul_Ioi (by linarith : -lam < 0) R).mul_const P
  have hi2 := (integrableOn_exp_mul_Ioi (by linarith : -(r / (16 * σ)) < 0) R).mul_const Q
  have hint : IntegrableOn (fun t => Real.exp ((-lam) * t) * P +
      Real.exp ((-(r / (16 * σ))) * t) * Q) (Set.Ioi R) := hi1.add hi2
  have hval : ∫ t in Set.Ioi R, (Real.exp ((-lam) * t) * P + Real.exp ((-(r / (16 * σ))) * t) * Q) =
      -Real.exp ((-lam) * R) / (-lam) * P +
        -Real.exp ((-(r / (16 * σ))) * R) / (-(r / (16 * σ))) * Q := by
    rw [integral_add hi1 hi2, integral_mul_const, integral_mul_const,
      integral_exp_mul_Ioi (by linarith), integral_exp_mul_Ioi (by linarith)]
  -- numerics
  have hPle : P ≤ 2 * Real.exp (lam ^ 2 * σ ^ 2 / 2) := by
    rw [hP, div_le_iff₀ hZ]
    have := mul_le_mul_of_nonneg_left hZg (by positivity : (0:ℝ) ≤ 2 * Real.exp (lam ^ 2 * σ ^ 2 / 2))
    linarith
  have hQle : Q ≤ T16 d r := by
    calc Q = Real.exp (-(3 * r ^ 2 / 8)) * I / Z := rfl
      _ ≤ Real.exp (-(3 * r ^ 2 / 8)) * I / (Real.sqrt (2 * Real.pi) * σ) ^ d :=
          div_le_div_of_nonneg_left (mul_nonneg hc0 hI0) hZg0 hZg
      _ ≤ Real.exp (-(3 * r ^ 2 / 8)) * (Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) *
            (d.factorial : ℝ) / (r / (16 * σ)) ^ d) / (Real.sqrt (2 * Real.pi) * σ) ^ d := by
          gcongr
          exact integral_exp_neg_mul_norm_le d ha0
      _ = T16 d r := by rw [cB16_eq d hσ hr0]; field_simp
  have hT : T16 d r * (4 * (n:ℝ)) ≤ 1 := T16_bound hd hdn
  have hT0 : 0 ≤ T16 d r := by unfold T16; positivity
  have hexp1 : Real.exp ((-lam) * R) * Real.exp (lam ^ 2 * σ ^ 2 / 2) ≤ 1 / n := by
    rw [← Real.exp_add]
    have e : (-lam) * R + lam ^ 2 * σ ^ 2 / 2 = -(R ^ 2 / (2 * σ ^ 2)) := by
      rw [hlam]; field_simp; ring
    have e2 : R ^ 2 / (2 * σ ^ 2) = 8 * Real.log n := by rw [hR2]; field_simp; ring
    rw [e, e2]
    calc Real.exp (-(8 * Real.log n)) ≤ Real.exp (-Real.log n) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / n := by rw [Real.exp_neg, Real.exp_log hnpos, one_div]
  have t1 : Real.exp ((-lam) * R) / lam * P ≤ σ / (2 * n) := by
    calc Real.exp ((-lam) * R) / lam * P
        ≤ Real.exp ((-lam) * R) / lam * (2 * Real.exp (lam ^ 2 * σ ^ 2 / 2)) := by gcongr
      _ = 2 * (Real.exp ((-lam) * R) * Real.exp (lam ^ 2 * σ ^ 2 / 2)) / lam := by ring
      _ ≤ 2 * (1 / n) / lam := by gcongr
      _ = 2 * σ ^ 2 / (n * R) := by rw [hlam]; field_simp
      _ ≤ σ / (2 * n) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hR4 (by positivity : (0:ℝ) ≤ σ * n)]
  have hexpa : Real.exp ((-(r / (16 * σ))) * R) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have t2 : Real.exp ((-(r / (16 * σ))) * R) / (r / (16 * σ)) * Q ≤ σ / n := by
    calc Real.exp ((-(r / (16 * σ))) * R) / (r / (16 * σ)) * Q
        ≤ 1 / (r / (16 * σ)) * T16 d r :=
          mul_le_mul ((div_le_div_iff_of_pos_right ha0).mpr hexpa) hQle hQ0 (by positivity)
      _ = 16 * σ / r * T16 d r := by field_simp
      _ ≤ 4 * σ * T16 d r := by
          gcongr
          rw [div_le_iff₀ hr0]; nlinarith
      _ ≤ σ / n := by
          rw [le_div_iff₀ hnpos]
          have := mul_le_mul_of_nonneg_left hT hσ.le
          linarith
  calc ∫⁻ t in Set.Ioi R, densityMeasure (lgPdf abar σ r) {x | t ≤ |⟪x - abar, θ⟫|}
      ≤ ∫⁻ t in Set.Ioi R, ENNReal.ofReal (Real.exp ((-lam) * t) * P +
          Real.exp ((-(r / (16 * σ))) * t) * Q) :=
        lintegral_mono (fun t => tail_t abar hσ hr0 θ hθ hlam0.le t)
    _ = ENNReal.ofReal (∫ t in Set.Ioi R, (Real.exp ((-lam) * t) * P +
          Real.exp ((-(r / (16 * σ))) * t) * Q)) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun t =>
          add_nonneg (mul_nonneg (Real.exp_pos _).le hP0) (mul_nonneg (Real.exp_pos _).le hQ0)))).symm
    _ ≤ ENNReal.ofReal (R / n) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hval, neg_div_neg_eq, neg_div_neg_eq]
        have e : σ / (2 * n) + σ / n = (3 * σ / 2) / n := by field_simp; ring
        calc _ ≤ σ / (2 * n) + σ / n := add_le_add t1 t2
          _ = (3 * σ / 2) / n := e
          _ ≤ R / n := (div_le_div_iff_of_pos_right hnpos).mpr (by linarith)

end E9L45

open FriendlyShadow.Gaussian in
theorem solution {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) (σ : ℝ) (hσ : 0 < σ)
    (abar : EuclideanSpace ℝ (Fin d)) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hμ : μ = lgPdf abar σ (4 * Real.sqrt (d * Real.log n))) :
    IsDensity μ ∧ HasMean μ abar ∧
      LogLipschitz μ (4 * σ⁻¹ * Real.sqrt (d * Real.log n)) ∧
      CutoffRadiusLE μ abar (cutoffLevel n d) (4 * σ * Real.sqrt (d * Real.log n)) ∧
      NthDeviationLE μ abar n (4 * σ * Real.sqrt (Real.log n)) ∧
      LineVarianceGE μ (σ / 4) := by
  subst hμ
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hd.trans hdn
  have hnpos : (0:ℝ) < n := by linarith
  have hL : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]; linarith [Real.exp_one_lt_d9]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hr0 : 0 < 4 * Real.sqrt (d * Real.log n) := by
    have := Real.sqrt_pos.mpr (by nlinarith : (0:ℝ) < d * Real.log n)
    linarith
  refine ⟨E9L45.isDensity_lg abar hσ hr0, E9L45.hasMean_lg abar hσ hr0, ?_, ?_, E9L45.nthdev_lg hd hdn abar hσ,
    E9L45.linevar abar hσ hr0⟩
  · have e : 4 * σ⁻¹ * Real.sqrt (d * Real.log n) = 4 * Real.sqrt (d * Real.log n) / σ := by ring
    rw [e]; exact E9L45.loglip abar hσ hr0
  · unfold CutoffRadiusLE
    have e : 4 * σ * Real.sqrt (d * Real.log n) = 4 * Real.sqrt (d * Real.log n) * σ := by ring
    rw [e]
    refine (E9L45.cutoff_mass abar hσ hr0).trans (ENNReal.ofReal_le_ofReal ?_)
    unfold cutoffLevel
    have hC : 0 < (d:ℝ) * (n.choose d : ℝ) := by
      have := Nat.choose_pos hdn
      have h1 : (0:ℝ) < (n.choose d : ℝ) := by exact_mod_cast this
      positivity
    rw [le_div_iff₀ hC]
    exact E9L45.T_bound hd hdn
