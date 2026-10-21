-- Prove2me | solution 1 for BoundedNV.Uniform.cor1_expected_order
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:37:27.559376+00:00
-- url     : https://prove2.me/submissions/8bdf7368-539c-4a76-b789-0b441d73a265

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit
import Definitions.Def_BoundedNV_Uniform_UniformDemand

set_option autoImplicit false
open BoundedNV.Uniform ProbabilityTheory
open MeasureTheory

namespace BoundedNV.Uniform

lemma bnu2_expMin_eq (a b x : ℝ) (hab : a < b) :
    expMin (unifDensity a b) x = (∫ t in a..b, min t x) / (b - a) := by
  unfold expMin unifDensity
  have h : ∀ t : ℝ, min t x * (Set.Icc a b).indicator (fun _ => 1 / (b - a)) t =
      (Set.Icc a b).indicator (fun t => min t x * (1 / (b - a))) t := by
    intro t
    by_cases ht : t ∈ Set.Icc a b <;> simp [Set.indicator, ht]
  simp_rw [h]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_mul_const]
  ring

lemma bnu2_int_min_le (a b x : ℝ) (hab : a < b) (hx : x ≤ a) :
    ∫ t in a..b, min t x = (b - a) * x := by
  have : ∫ t in a..b, min t x = ∫ t in a..b, x := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab.le] at ht
    exact min_eq_right (by linarith [ht.1])
  rw [this]; simp

lemma bnu2_int_min_ge (a b x : ℝ) (hab : a < b) (hx : b ≤ x) :
    ∫ t in a..b, min t x = (b ^ 2 - a ^ 2) / 2 := by
  have : ∫ t in a..b, min t x = ∫ t in a..b, t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab.le] at ht
    exact min_eq_left (by linarith [ht.2])
  rw [this]; simp

lemma bnu2_int_min_mid (a b x : ℝ) (hax : a ≤ x) (hxb : x ≤ b) :
    ∫ t in a..b, min t x = (x ^ 2 - a ^ 2) / 2 + (b - x) * x := by
  have hc : Continuous fun t : ℝ => min t x := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ t in a..x, min t x = ∫ t in a..x, t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    exact min_eq_left ht.2
  have e2 : ∫ t in x..b, min t x = ∫ t in x..b, x := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxb] at ht
    exact min_eq_right ht.1
  rw [e1, e2]; simp

lemma bnu2_pi_le (a b p c x : ℝ) (hab : a < b) (hx : x ≤ a) :
    nvProfit (unifDensity a b) p c x = (p - c) * x := by
  unfold nvProfit
  rw [bnu2_expMin_eq a b x hab, bnu2_int_min_le a b x hab hx]
  have : b - a ≠ 0 := by linarith
  field_simp

lemma bnu2_pi_ge (a b p c x : ℝ) (hab : a < b) (hx : b ≤ x) :
    nvProfit (unifDensity a b) p c x = p * (a + b) / 2 - c * x := by
  unfold nvProfit
  rw [bnu2_expMin_eq a b x hab, bnu2_int_min_ge a b x hab hx]
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

lemma bnu2_pi_mid (a b p c x : ℝ) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    nvProfit (unifDensity a b) p c x =
      (-p / (2 * (b - a))) * x ^ 2 + (p * b / (b - a) - c) * x + (-p * a ^ 2 / (2 * (b - a))) := by
  unfold nvProfit
  rw [bnu2_expMin_eq a b x hab, bnu2_int_min_mid a b x hax hxb]
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

end BoundedNV.Uniform
namespace BoundedNV.Uniform

lemma bnu2_mu_bounds (a b p c : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p) :
    a < unifMu a b p c ∧ unifMu a b p c < b := by
  have hp : 0 < p := by linarith
  have h1 : 0 < c / p := div_pos hc hp
  have h2 : c / p < 1 := (div_lt_one hp).2 hcp
  unfold unifMu
  constructor
  · nlinarith [mul_pos (sub_pos.2 h2) (sub_pos.2 hab)]
  · nlinarith [mul_pos h1 (sub_pos.2 hab)]

lemma bnu2_mid_diff (a b p c x : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p)
    (hax : a ≤ x) (hxb : x ≤ b) :
    nvProfit (unifDensity a b) p c (unifMu a b p c) - nvProfit (unifDensity a b) p c x =
      p / (2 * (b - a)) * (x - unifMu a b p c) ^ 2 := by
  obtain ⟨h1, h2⟩ := bnu2_mu_bounds a b p c hab hc hcp
  rw [bnu2_pi_mid a b p c x hab hax hxb, bnu2_pi_mid a b p c _ hab h1.le h2.le]
  have hp : p ≠ 0 := by intro h; linarith
  have hba : b - a ≠ 0 := by intro h; linarith
  unfold unifMu
  field_simp
  ring

lemma bnu2_strict (a b p c x : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p)
    (hx : x ≠ unifMu a b p c) :
    nvProfit (unifDensity a b) p c x < nvProfit (unifDensity a b) p c (unifMu a b p c) := by
  obtain ⟨h1, h2⟩ := bnu2_mu_bounds a b p c hab hc hcp
  have hp : 0 < p := by linarith
  have hba : 0 < b - a := by linarith
  have hpos : ∀ y, y ≠ unifMu a b p c → 0 < p / (2 * (b - a)) * (y - unifMu a b p c) ^ 2 := by
    intro y hy
    have : y - unifMu a b p c ≠ 0 := sub_ne_zero.2 hy
    positivity
  by_cases hxa : x ≤ a
  · have e1 := bnu2_pi_le a b p c x hab hxa
    have e2 := bnu2_pi_le a b p c a hab le_rfl
    have e3 := bnu2_mid_diff a b p c a hab hc hcp le_rfl hab.le
    have := hpos a (ne_of_lt h1)
    nlinarith
  · by_cases hxb : b ≤ x
    · have e1 := bnu2_pi_ge a b p c x hab hxb
      have e2 := bnu2_pi_ge a b p c b hab le_rfl
      have e3 := bnu2_mid_diff a b p c b hab hc hcp hab.le le_rfl
      have := hpos b (ne_of_gt h2)
      nlinarith
    · have := bnu2_mid_diff a b p c x hab hc hcp (le_of_not_ge hxa) (le_of_not_ge hxb)
      have := hpos x hx
      linarith

lemma bnu2_sigma_sq (a b p β : ℝ) (hab : a < b) (hp : 0 < p) (hβ : 0 < β) :
    unifSigma a b p β ^ 2 = β * (b - a) / p := by
  unfold unifSigma
  rw [Real.sq_sqrt]
  have : 0 < b - a := by linarith
  positivity

lemma bnu2_key (a b p c β : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p) (hβ : 0 < β) :
    ∀ t ∈ Set.Icc a b, Real.exp (nvProfit (unifDensity a b) p c t / β) =
      Real.exp (nvProfit (unifDensity a b) p c (unifMu a b p c) / β) *
        Real.exp (-(t - unifMu a b p c) ^ 2 / (2 * unifSigma a b p β ^ 2)) := by
  intro t ht
  have hp : 0 < p := by linarith
  have hba : 0 < b - a := by linarith
  rw [← Real.exp_add]
  congr 1
  have h := bnu2_mid_diff a b p c t hab hc hcp ht.1 ht.2
  rw [bnu2_sigma_sq a b p β hab hp hβ]
  have : nvProfit (unifDensity a b) p c t =
      nvProfit (unifDensity a b) p c (unifMu a b p c) - p / (2 * (b - a)) * (t - unifMu a b p c) ^ 2 := by
    linarith
  rw [this]
  field_simp
  ring

lemma bnu2_cdf (a b μ : ℝ) (hab : a < b) (h1 : a ≤ μ) (h2 : μ ≤ b) :
    demandCDF (unifDensity a b) μ = (μ - a) / (b - a) := by
  unfold demandCDF unifDensity
  rw [setIntegral_indicator measurableSet_Icc]
  have : Set.Iic μ ∩ Set.Icc a b = Set.Icc a μ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
    · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
  rw [this, setIntegral_const, Real.volume_real_Icc_of_le h1, smul_eq_mul]
  ring

end BoundedNV.Uniform
namespace BoundedNV.Uniform

noncomputable def bnu2_g (μ σ y : ℝ) : ℝ := Real.exp (-(y - μ) ^ 2 / (2 * σ ^ 2))

lemma bnu2_g_cont (μ σ : ℝ) : Continuous (bnu2_g μ σ) := by
  unfold bnu2_g; fun_prop

lemma bnu2_G_pos (μ σ a b : ℝ) (hab : a < b) : 0 < ∫ y in a..b, bnu2_g μ σ y := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (bnu2_g_cont μ σ).intervalIntegrable _ _
  · intro y _; exact Real.exp_pos _
  · exact hab

lemma bnu2_ftc (μ σ a b : ℝ) (hσ : σ ≠ 0) :
    ∫ y in a..b, (y - μ) * bnu2_g μ σ y = σ ^ 2 * (bnu2_g μ σ a - bnu2_g μ σ b) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => -σ ^ 2 * bnu2_g μ σ y) ((y - μ) * bnu2_g μ σ y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y - μ) ^ 2) (2 * (y - μ)) y := by
      have := ((hasDerivAt_id' y).sub_const μ).pow 2
      refine this.congr_deriv ?_
      norm_num
    have h2 := (h1.neg.div_const (2 * σ ^ 2)).exp.const_mul (-σ ^ 2)
    have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
    exact h2.congr_deriv (by unfold bnu2_g; simp only [Pi.neg_apply]; field_simp <;> ring)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (((by unfold bnu2_g; fun_prop : Continuous fun y : ℝ => (y - μ) * bnu2_g μ σ y)).intervalIntegrable a b)
  rw [this]; ring

lemma bnu2_num (μ σ a b : ℝ) (hσ : σ ≠ 0) :
    ∫ y in a..b, y * bnu2_g μ σ y =
      σ ^ 2 * (bnu2_g μ σ a - bnu2_g μ σ b) + μ * ∫ y in a..b, bnu2_g μ σ y := by
  have h : ∀ y : ℝ, y * bnu2_g μ σ y = (y - μ) * bnu2_g μ σ y + μ * bnu2_g μ σ y := fun y => by ring
  simp_rw [h]
  have c1 : Continuous fun y : ℝ => (y - μ) * bnu2_g μ σ y := by unfold bnu2_g; fun_prop
  have c2 : Continuous fun y : ℝ => μ * bnu2_g μ σ y := by unfold bnu2_g; fun_prop
  rw [intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, bnu2_ftc μ σ a b hσ]

lemma bnu2_logitExp (a b p c β : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p) (hβ : 0 < β) :
    logitExp (Set.Icc a b) (nvProfit (unifDensity a b) p c) β id =
      (∫ y in a..b, y * bnu2_g (unifMu a b p c) (unifSigma a b p β) y) /
        (∫ y in a..b, bnu2_g (unifMu a b p c) (unifSigma a b p β) y) := by
  have key : ∀ t ∈ Set.Icc a b, Real.exp (nvProfit (unifDensity a b) p c t / β) =
      Real.exp (nvProfit (unifDensity a b) p c (unifMu a b p c) / β) *
        bnu2_g (unifMu a b p c) (unifSigma a b p β) t := bnu2_key a b p c β hab hc hcp hβ
  have hG := bnu2_G_pos (unifMu a b p c) (unifSigma a b p β) a b hab
  have hZ : ∫ v in Set.Icc a b, Real.exp (nvProfit (unifDensity a b) p c v / β) =
      Real.exp (nvProfit (unifDensity a b) p c (unifMu a b p c) / β) *
        ∫ y in a..b, bnu2_g (unifMu a b p c) (unifSigma a b p β) y := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => key t ht), integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  unfold logitExp logitDensity
  have h1 : ∀ y : ℝ, id y * (Set.Icc a b).indicator (fun y => Real.exp (nvProfit (unifDensity a b) p c y / β) /
        ∫ v in Set.Icc a b, Real.exp (nvProfit (unifDensity a b) p c v / β)) y =
      (Set.Icc a b).indicator (fun y => y * (Real.exp (nvProfit (unifDensity a b) p c y / β) /
        ∫ v in Set.Icc a b, Real.exp (nvProfit (unifDensity a b) p c v / β))) y := by
    intro y
    by_cases h : y ∈ Set.Icc a b <;> simp [Set.indicator, h]
  simp_rw [h1]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le, hZ]
  have hK := Real.exp_pos (nvProfit (unifDensity a b) p c (unifMu a b p c) / β)
  have : ∫ y in a..b, y * (Real.exp (nvProfit (unifDensity a b) p c y / β) /
        (Real.exp (nvProfit (unifDensity a b) p c (unifMu a b p c) / β) *
          ∫ y in a..b, bnu2_g (unifMu a b p c) (unifSigma a b p β) y)) =
      ∫ y in a..b, (y * bnu2_g (unifMu a b p c) (unifSigma a b p β) y) /
        (∫ y in a..b, bnu2_g (unifMu a b p c) (unifSigma a b p β) y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hab.le] at hy
    simp only
    rw [key y hy]
    field_simp
  rw [this, intervalIntegral.integral_div]

end BoundedNV.Uniform
namespace BoundedNV.Uniform

open ProbabilityTheory

lemma bnu2_pdf (z : ℝ) : gaussianPDFReal 0 1 z = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) := by
  simp [gaussianPDFReal]

lemma bnu2_dPhi (A B : ℝ) (hAB : A ≤ B) :
    cdf (gaussianReal 0 1) B - cdf (gaussianReal 0 1) A = ∫ z in A..B, gaussianPDFReal 0 1 z := by
  have h1 : (gaussianReal 0 1) (Set.Ioc A B) = ENNReal.ofReal (cdf (gaussianReal 0 1) B - cdf (gaussianReal 0 1) A) := by
    rw [← measure_cdf (gaussianReal 0 1)]
    rw [StieltjesFunction.measure_Ioc]
    rw [measure_cdf]
  have h2 := gaussianReal_apply_eq_integral 0 (one_ne_zero : (1 : NNReal) ≠ 0) (Set.Ioc A B)
  rw [h1] at h2
  have hnn1 : 0 ≤ cdf (gaussianReal 0 1) B - cdf (gaussianReal 0 1) A :=
    sub_nonneg.2 (monotone_cdf _ hAB)
  have hnn2 : 0 ≤ ∫ z in Set.Ioc A B, gaussianPDFReal 0 1 z :=
    integral_nonneg (fun z => gaussianPDFReal_nonneg _ _ _)
  rw [ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2] at h2
  rw [h2, intervalIntegral.integral_of_le hAB]

lemma bnu2_G_eq (μ σ a b : ℝ) (hσ : 0 < σ) (hab : a < b) :
    ∫ y in a..b, bnu2_g μ σ y =
      σ * Real.sqrt (2 * Real.pi) *
        (cdf (gaussianReal 0 1) ((b - μ) / σ) - cdf (gaussianReal 0 1) ((a - μ) / σ)) := by
  have hs2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h1 : ∀ y : ℝ, bnu2_g μ σ y = Real.sqrt (2 * Real.pi) * gaussianPDFReal 0 1 (y / σ - μ / σ) := by
    intro y
    rw [bnu2_pdf]
    unfold bnu2_g
    rw [← mul_assoc, mul_inv_cancel₀ hs2.ne', one_mul]
    congr 1
    field_simp
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div_sub (fun z => gaussianPDFReal 0 1 z) hσ.ne' (μ / σ)]
  have hA : a / σ - μ / σ = (a - μ) / σ := (sub_div a μ σ).symm
  have hB : b / σ - μ / σ = (b - μ) / σ := (sub_div b μ σ).symm
  rw [hA, hB, ← bnu2_dPhi _ _ (by apply div_le_div_of_nonneg_right <;> linarith), smul_eq_mul]
  ring

lemma bnu2_gaussian_g (μ σ y : ℝ) (hσ : 0 < σ) :
    bnu2_g μ σ y = Real.sqrt (2 * Real.pi) * gaussianPDFReal 0 1 ((y - μ) / σ) := by
  have hs2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  rw [bnu2_pdf]
  unfold bnu2_g
  rw [← mul_assoc, mul_inv_cancel₀ hs2.ne', one_mul]
  congr 1
  field_simp

end BoundedNV.Uniform

theorem solution (a b p c β μ σ : ℝ) (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c) (hcp : c < p)
    (hβ : 0 < β) (hμ : μ = unifMu a b p c) (hσ : σ = unifSigma a b p β) :
    logitExp (Set.Icc a b) (nvProfit (unifDensity a b) p c) β id =
      μ - σ * (gaussianPDFReal 0 1 ((b - μ) / σ) - gaussianPDFReal 0 1 ((a - μ) / σ)) /
        (cdf (gaussianReal 0 1) ((b - μ) / σ) - cdf (gaussianReal 0 1) ((a - μ) / σ)) := by
  have hp : 0 < p := by linarith
  have hσpos : 0 < σ := by
    rw [hσ]; unfold unifSigma
    have : 0 < β * (b - a) / p := by
      have : 0 < b - a := by linarith
      positivity
    exact Real.sqrt_pos.2 this
  rw [bnu2_logitExp a b p c β hab hc hcp hβ, ← hμ, ← hσ, bnu2_num μ σ a b hσpos.ne',
    bnu2_G_eq μ σ a b hσpos hab, bnu2_gaussian_g μ σ a hσpos, bnu2_gaussian_g μ σ b hσpos]
  have hG := bnu2_G_pos μ σ a b hab
  rw [bnu2_G_eq μ σ a b hσpos hab] at hG
  have hs2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hΔ : 0 < cdf (gaussianReal 0 1) ((b - μ) / σ) - cdf (gaussianReal 0 1) ((a - μ) / σ) := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos hσpos hs2]
  field_simp
  ring
