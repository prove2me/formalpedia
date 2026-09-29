-- Prove2me | solution 2 for ErlerGross.mode_sum_eq_B3_identity
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T21:59:18.825092+00:00
-- url     : https://prove2.me/submissions/aca4d6c6-e53f-4104-953b-cf6824d4cb34

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_B3_series_closed_form
import Theorems.Thm_ErlerGross_B3_cubic_reciprocal_series_closed_form

noncomputable section
/- BEGIN INLINE EGCoeffModeBridge.lean -/
open Real Filter Topology MeasureTheory
open ErlerGross

open Real Filter Topology MeasureTheory

set_option autoImplicit false

/--
A Tonelli lemma for a nonnegative power-series on `(0,1)`.  The hypotheses are deliberately
stated on `Ioo 0 1`: the endpoint values are irrelevant for Lebesgue integration, while
`integral_Ioc_eq_integral_Ioo` below is what identifies the resulting integral with the
usual interval integral.
-/
theorem eg_coeff_sum_generic
    (b : ℕ → ℝ) (f : ℝ → ℝ)
    (hb : ∀ n : ℕ, 0 ≤ b n)
    (hf_int : IntegrableOn f (Set.Ioo (0 : ℝ) 1))
    (hf_nonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ f x)
    (hf_point : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      f x = ∑' n : ℕ, b (n + 1) * x ^ (2 * n + 1))
    (hf_summable : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun n : ℕ => b (n + 1) * x ^ (2 * n + 1))) :
    HasSum (fun n : ℕ => b (n + 1) / (n + 1))
      (2 * ∫ x in (0 : ℝ)..1, f x) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  have hf_int' : Integrable f μ := by
    simpa [μ] using hf_int.integrable
  have hf_nonneg' : 0 ≤ᵐ[μ] f := by
    exact ae_restrict_of_forall_mem measurableSet_Ioo hf_nonneg
  have hf_point' : f =ᵐ[μ] (fun x => ∑' n : ℕ, b (n + 1) * x ^ (2 * n + 1)) := by
    exact ae_restrict_of_forall_mem measurableSet_Ioo hf_point
  have hg_cont (n : ℕ) : Continuous (fun x : ℝ => b (n + 1) * x ^ (2 * n + 1)) := by
    fun_prop
  have hg_meas (n : ℕ) : Measurable (fun x : ℝ => b (n + 1) * x ^ (2 * n + 1)) :=
    (hg_cont n).measurable
  have hg_int (n : ℕ) : Integrable (fun x : ℝ => b (n + 1) * x ^ (2 * n + 1)) μ := by
    have hIcc : IntegrableOn (fun x : ℝ => b (n + 1) * x ^ (2 * n + 1))
        (Set.Icc (0 : ℝ) 1) := (hg_cont n).integrableOn_Icc
    have hIoo : IntegrableOn (fun x : ℝ => b (n + 1) * x ^ (2 * n + 1))
        (Set.Ioo (0 : ℝ) 1) := hIcc.mono_set Set.Ioo_subset_Icc_self
    simpa [μ] using hIoo.integrable
  have hg_nonneg (n : ℕ) : 0 ≤ᵐ[μ] (fun x : ℝ => b (n + 1) * x ^ (2 * n + 1)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro x hx
    exact mul_nonneg (hb (n + 1)) (pow_nonneg hx.1.le _)
  have htonelli :
      (∫⁻ x, ∑' n : ℕ, ENNReal.ofReal (b (n + 1) * x ^ (2 * n + 1)) ∂μ) =
        ∑' n : ℕ, ∫⁻ x, ENNReal.ofReal (b (n + 1) * x ^ (2 * n + 1)) ∂μ := by
    apply lintegral_tsum
    intro n
    exact (hg_meas n).ennreal_ofReal.aemeasurable
  have hpoint_enn :
      (fun x => ENNReal.ofReal (f x)) =ᵐ[μ]
        (fun x => ∑' n : ℕ, ENNReal.ofReal (b (n + 1) * x ^ (2 * n + 1))) := by
    filter_upwards [hf_point', ae_restrict_of_forall_mem measurableSet_Ioo
      (fun x hx => hx)] with x hx hxIoo
    rw [hx, ENNReal.ofReal_tsum_of_nonneg]
    · intro n
      exact mul_nonneg (hb (n + 1)) (pow_nonneg hxIoo.1.le _)
    · exact hf_summable x hxIoo
  have h_ofReal_integral :
      ENNReal.ofReal (∫ x, f x ∂μ) =
        ∑' n : ℕ, ENNReal.ofReal (∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ) := by
    calc
      ENNReal.ofReal (∫ x, f x ∂μ) =
          ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf_int' hf_nonneg'
      _ = ∫⁻ x, ∑' n : ℕ, ENNReal.ofReal (b (n + 1) * x ^ (2 * n + 1)) ∂μ :=
        lintegral_congr_ae hpoint_enn
      _ = ∑' n : ℕ, ∫⁻ x, ENNReal.ofReal (b (n + 1) * x ^ (2 * n + 1)) ∂μ :=
        htonelli
      _ = ∑' n : ℕ, ENNReal.ofReal (∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ) := by
        apply tsum_congr
        intro n
        exact (ofReal_integral_eq_lintegral_ofReal (hg_int n) (hg_nonneg n)).symm
  have hf_integral_nonneg : 0 ≤ ∫ x, f x ∂μ := integral_nonneg_of_ae hf_nonneg'
  have hg_integral_nonneg (n : ℕ) :
      0 ≤ ∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ := integral_nonneg_of_ae (hg_nonneg n)
  let A : NNReal := ⟨∫ x, f x ∂μ, hf_integral_nonneg⟩
  let a : ℕ → NNReal := fun n =>
    ⟨∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ, hg_integral_nonneg n⟩
  have htarget_coe :
      ENNReal.ofReal (∫ x, f x ∂μ) = (A : ENNReal) := by
    change ENNReal.ofReal (∫ x, f x ∂μ) =
      (↑(NNReal.mk (∫ x, f x ∂μ) hf_integral_nonneg) : ENNReal)
    exact ENNReal.ofReal_eq_coe_nnreal hf_integral_nonneg
  have hterm_coe (n : ℕ) :
      ENNReal.ofReal (∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ) = (a n : ENNReal) := by
    change ENNReal.ofReal (∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ) =
      (↑(NNReal.mk (∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ)
        (hg_integral_nonneg n)) : ENNReal)
    exact ENNReal.ofReal_eq_coe_nnreal (hg_integral_nonneg n)
  have hAeq : (A : ENNReal) = ∑' n : ℕ, (a n : ENNReal) := by
    rw [← htarget_coe]
    simpa only [hterm_coe] using h_ofReal_integral
  have ha_summable : Summable a := by
    apply ENNReal.tsum_coe_ne_top_iff_summable.mp
    rw [← hAeq]
    exact ENNReal.coe_ne_top
  have htsum : (∑' n : ℕ, a n) = A := by
    apply ENNReal.coe_injective
    calc
      (↑(∑' n : ℕ, a n) : ENNReal) = ∑' n : ℕ, (a n : ENNReal) :=
        ENNReal.coe_tsum ha_summable
      _ = (A : ENNReal) := hAeq.symm
  have ha_hasSum : HasSum a A := ha_summable.hasSum_iff.mpr htsum
  have hreal :
      HasSum (fun n : ℕ => ∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ)
        (∫ x, f x ∂μ) := by
    have hreal' := (NNReal.hasSum_coe.mpr ha_hasSum)
    have ha_coe (n : ℕ) :
        (a n : ℝ) = ∫ x, b (n + 1) * x ^ (2 * n + 1) ∂μ := by
      rfl
    have hA_coe : (A : ℝ) = ∫ x, f x ∂μ := by
      rfl
    simpa only [ha_coe, hA_coe] using hreal'
  have hμ_interval (g : ℝ → ℝ) :
      (∫ x, g x ∂μ) = ∫ x in (0 : ℝ)..1, g x := by
    dsimp [μ]
    rw [← integral_Ioc_eq_integral_Ioo]
    exact (intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)).symm
  have hreal_interval :
      HasSum (fun n : ℕ => ∫ x in (0 : ℝ)..1, b (n + 1) * x ^ (2 * n + 1))
        (∫ x in (0 : ℝ)..1, f x) := by
    simpa only [hμ_interval] using hreal
  have hterm_formula (n : ℕ) :
      (∫ x in (0 : ℝ)..1, b (n + 1) * x ^ (2 * n + 1)) =
        b (n + 1) / (2 * (n + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hterm_formula' :
      HasSum (fun n : ℕ => b (n + 1) / (2 * (n + 1)))
        (∫ x in (0 : ℝ)..1, f x) := by
    convert hreal_interval using 1
    · funext n
      exact (hterm_formula n).symm
  have hscaled := hterm_formula'.mul_left (2 : ℝ)
  have hterm_scaled (n : ℕ) :
      (2 : ℝ) * (b (n + 1) / (2 * (n + 1))) = b (n + 1) / (n + 1) := by
    have hn : (0 : ℝ) < n + 1 := by positivity
    field_simp
  simpa only [hterm_scaled] using hscaled

/-- Convenience form using the even-power expansion from the Erler--Gross setup. -/
theorem eg_coeff_sum_from_even_expansion
    (b : ℕ → ℝ) (H : ℝ → ℝ)
    (hb : ∀ n : ℕ, 0 ≤ b n)
    (hseries : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      H x - 1 = ∑' n : ℕ, b (n + 1) * x ^ (2 * (n + 1)))
    (hseries_summable : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun n : ℕ => b (n + 1) * x ^ (2 * (n + 1))))
    (h_int : IntegrableOn (fun x : ℝ => (H x - 1) / x) (Set.Ioo (0 : ℝ) 1)) :
    HasSum (fun n : ℕ => b (n + 1) / (n + 1))
      (2 * ∫ x in (0 : ℝ)..1, (H x - 1) / x) := by
  have hpow (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
      b (n + 1) * x ^ (2 * (n + 1)) / x = b (n + 1) * x ^ (2 * n + 1) := by
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, pow_succ]
    field_simp [hx0]
  have hodd_summable (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      Summable (fun n : ℕ => b (n + 1) * x ^ (2 * n + 1)) := by
    have hs := (hseries_summable x hx).mul_right x⁻¹
    apply hs.congr
    intro n
    simpa [div_eq_mul_inv] using hpow x hx n
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      (H x - 1) / x = ∑' n : ℕ, b (n + 1) * x ^ (2 * n + 1) := by
    calc
      (H x - 1) / x = (∑' n : ℕ, b (n + 1) * x ^ (2 * (n + 1))) / x := by
        rw [hseries x hx]
      _ = (∑' n : ℕ, b (n + 1) * x ^ (2 * (n + 1))) * x⁻¹ := by
        rw [div_eq_mul_inv]
      _ = ∑' n : ℕ, (b (n + 1) * x ^ (2 * (n + 1))) * x⁻¹ := by
        exact (tsum_mul_right).symm
      _ = ∑' n : ℕ, b (n + 1) * x ^ (2 * n + 1) := by
        apply tsum_congr
        intro n
        simpa [div_eq_mul_inv] using hpow x hx n
  have hnonneg (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      0 ≤ (H x - 1) / x := by
    rw [hpoint x hx]
    apply tsum_nonneg
    intro n
    exact mul_nonneg (hb (n + 1)) (pow_nonneg hx.1.le _)
  exact eg_coeff_sum_generic b (fun x => (H x - 1) / x) hb h_int hnonneg hpoint hodd_summable
open Real Filter Topology MeasureTheory

namespace ErlerGross

lemma term_eq_neumann_generating (m : ℕ) (hm : 0 < m) :
    3 * neumannMEven m * betaVec (2 * m) =
      - ((-1 : ℝ)^m * neumannA (2 * m) / m) := by
  rw [neumannMEven, betaVec]
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [hcast]
  have hcos : Real.cos (2 * (m : ℝ) * Real.pi / 2) = (-1 : ℝ)^m := by
    rw [show 2 * (m : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi by ring]
    exact Real.cos_nat_mul_pi m
  rw [hcos]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : Real.sqrt (2 * (m : ℝ)) ^ 2 = 2 * (m : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_ne : Real.sqrt (2 * (m : ℝ)) ≠ 0 := by positivity
  field_simp [hsqrt_ne]
  rw [hsqrt]
  ring

end ErlerGross

namespace ErlerGross

lemma mode_sum_eq_H_integral
    (b : ℕ → ℝ) (H : ℝ → ℝ)
    (hbridge : ∀ m : ℕ, b m = (-1 : ℝ)^m * neumannA (2*m))
    (hseries : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      H x - 1 = ∑' n : ℕ, b (n + 1) * x ^ (2 * (n + 1)))
    (hseries_summable : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun n : ℕ => b (n + 1) * x ^ (2 * (n + 1))))
    (hb : ∀ n : ℕ, 0 ≤ b n)
    (h_int : IntegrableOn (fun x : ℝ => (H x - 1) / x)
      (Set.Ioo (0 : ℝ) 1)) :
    HasSum
      (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
      (-2 * ∫ x in (0 : ℝ)..1, (H x - 1) / x) := by
  have hc := eg_coeff_sum_from_even_expansion b H hb hseries hseries_summable h_int
  have hcneg := hc.neg
  have hmode : HasSum
      (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
      (-(2 * ∫ x in (0 : ℝ)..1, (H x - 1) / x)) := by
    apply hcneg.congr_fun
    intro n
    rw [term_eq_neumann_generating (m := n + 1) (by positivity)]
    rw [hbridge]
    push_cast
    ring
  simpa only [neg_mul] using hmode

end ErlerGross

namespace ErlerGross

lemma eg_mode_sum_from_H_expansion
    (H : ℝ → ℝ)
    (hseries : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      H x - 1 = ∑' n : ℕ,
        ((-1 : ℝ) ^ (n + 1) * neumannA (2 * (n + 1))) *
          x ^ (2 * (n + 1)))
    (hseries_summable : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun n : ℕ =>
        ((-1 : ℝ) ^ (n + 1) * neumannA (2 * (n + 1))) *
          x ^ (2 * (n + 1))))
    (hb : ∀ n : ℕ, 0 ≤ (-1 : ℝ)^n * neumannA (2*n))
    (h_int : IntegrableOn (fun x : ℝ => (H x - 1) / x)
      (Set.Ioo (0 : ℝ) 1)) :
    HasSum
      (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
      (-2 * ∫ x in (0 : ℝ)..1, (H x - 1) / x) := by
  apply mode_sum_eq_H_integral
      (b := fun n : ℕ => (-1 : ℝ)^n * neumannA (2*n)) H
  · intro m
    rfl
  · intro x hx
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hseries x hx
  · intro x hx
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hseries_summable x hx
  · exact hb
  · exact h_int

end ErlerGross

namespace ErlerGross

lemma mode_sum_eq_B3_of_H_expansion
    (H : ℝ → ℝ)
    (hseries : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      H x - 1 = ∑' n : ℕ,
        ((-1 : ℝ) ^ (n + 1) * neumannA (2 * (n + 1))) *
          x ^ (2 * (n + 1)))
    (hseries_summable : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun n : ℕ =>
        ((-1 : ℝ) ^ (n + 1) * neumannA (2 * (n + 1))) *
          x ^ (2 * (n + 1))))
    (hb : ∀ n : ℕ, 0 ≤ (-1 : ℝ)^n * neumannA (2*n))
    (h_int : IntegrableOn (fun x : ℝ => (H x - 1) / x)
      (Set.Ioo (0 : ℝ) 1))
    (h_eval : -2 * ∫ x in (0 : ℝ)..1, (H x - 1) / x =
      2 * ∑' n : ℕ, b3Term (n + 1)) :
    HasSum
      (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
      (2 * ∑' n : ℕ, b3Term (n + 1)) := by
  have h := eg_mode_sum_from_H_expansion H hseries hseries_summable hb h_int
  rw [h_eval] at h
  exact h

end ErlerGross
/- END INLINE EGCoeffModeBridge.lean -/

/- BEGIN INLINE ErlerGross_weighted_reduction.lean -/

open Complex Set
open scoped Topology

lemma cayley_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) :
    (1 + z * I) / (1 - z * I) ∈ slitPlane := by
  have hden : 1 - z * I ≠ 0 := by
    intro h
    have hzI0 := sub_eq_zero.mp h
    have hzI : z * I = 1 := hzI0.symm
    have hn := congrArg norm hzI
    have hz1 : ‖z‖ = 1 := by simpa [norm_mul, Complex.norm_I] using hn
    linarith
  have hdenpos : 0 < Complex.normSq (1 - z * I) :=
    Complex.normSq_pos.mpr hden
  have hzsq : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have hsq : ‖z‖ ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg z) (by norm_num)).mpr hz
    nlinarith
  rw [Complex.mem_slitPlane_iff]
  left
  rw [Complex.div_re]
  have hnum :
      (1 + z * I).re * (1 - z * I).re +
          (1 + z * I).im * (1 - z * I).im =
        1 - Complex.normSq z := by
    simp [Complex.normSq_apply]
    ring
  rw [← add_div, hnum]
  have hnumpos : 0 < (1 : ℝ) - Complex.normSq z := by linarith
  exact div_pos hnumpos hdenpos

lemma analyticAt_complex_arctan_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ Complex.arctan z := by
  unfold Complex.arctan
  have hnum : AnalyticAt ℂ (fun z : ℂ => 1 + z * I) z :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hden : AnalyticAt ℂ (fun z : ℂ => 1 - z * I) z :=
    analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
  have hden0 : (1 - z * I) ≠ 0 := by
    intro h
    have hzI0 := sub_eq_zero.mp h
    have hzI : z * I = 1 := hzI0.symm
    have hn := congrArg norm hzI
    have hz1 : ‖z‖ = 1 := by simpa [norm_mul, Complex.norm_I] using hn
    linarith
  have hq : AnalyticAt ℂ (fun z : ℂ => (1 + z * I) / (1 - z * I)) z :=
    hnum.div hden hden0
  have hlog := hq.clog (cayley_mem_slitPlane hz)
  have hsmul :
      ((-I / 2 : ℂ) • (fun w : ℂ => Complex.log ((1 + w * I) / (1 - w * I)))) =
        (fun w : ℂ => -I / 2 * Complex.log ((1 + w * I) / (1 - w * I))) := by
    funext w
    simp [smul_eq_mul]
  rw [← hsmul]
  exact hlog.const_smul

lemma analyticAt_cos_two_thirds_arctan_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (fun w : ℂ => Complex.cos ((2 / 3 : ℂ) * Complex.arctan w)) z := by
  have ha := analyticAt_complex_arctan_of_norm_lt_one hz
  have hscale :
      AnalyticAt ℂ (fun w : ℂ => (2 / 3 : ℂ) * Complex.arctan w) z := by
    have hsmul := ha.const_smul (c := (2 / 3 : ℂ))
    have heq :
        ((2 / 3 : ℂ) • (fun w : ℂ => Complex.arctan w)) =
          (fun w : ℂ => (2 / 3 : ℂ) * Complex.arctan w) := by
      funext w
      simp [smul_eq_mul]
    rw [heq] at hsmul
    exact hsmul
  simpa only [Function.comp_def] using (Complex.analyticAt_cos.comp hscale)

noncomputable def egComplexF (w : ℂ) : ℂ :=
  Complex.cos ((2 / 3 : ℂ) * Complex.arctan w)

lemma egComplexF_analyticOn_ball :
    AnalyticOn ℂ egComplexF (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  exact (analyticAt_cos_two_thirds_arctan_of_norm_lt_one
    (z := w) (by simpa [Metric.mem_ball] using hw)).analyticWithinAt

lemma egComplexF_hasSum_taylor {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ =>
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n egComplexF 0 * w ^ n)
      (egComplexF w) := by
  have hdiff : DifferentiableOn ℂ egComplexF (Metric.ball (0 : ℂ) 1) :=
    egComplexF_analyticOn_ball.differentiableOn
  have hz : w ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball] using hw
  have h := Complex.hasSum_taylorSeries_on_ball (c := (0 : ℂ)) (r := (1 : ℝ)) hdiff hz
  simpa only [sub_zero, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

lemma egComplexF_ofReal (x : ℝ) :
    egComplexF (x : ℂ) = (Real.cos (2 / 3 * Real.arctan x) : ℂ) := by
  rw [egComplexF]
  have harc : Complex.arctan (x : ℂ) = (Real.arctan x : ℂ) :=
    (Complex.ofReal_arctan x).symm
  rw [harc]
  have harg :
      (2 / 3 : ℂ) * (Real.arctan x : ℂ) =
        ((2 / 3 * Real.arctan x : ℝ) : ℂ) := by norm_num
  rw [harg, Complex.ofReal_cos]

lemma egReal_restriction :
    (fun x : ℝ => (egComplexF (x : ℂ)).re) =
      (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) := by
  funext x
  calc
    (egComplexF (x : ℂ)).re = ((Real.cos (2 / 3 * Real.arctan x) : ℝ) : ℂ).re :=
      congrArg Complex.re (egComplexF_ofReal x)
    _ = Real.cos (2 / 3 * Real.arctan x) := Complex.ofReal_re _

lemma neumannA_even_eq (m : ℕ) :
    ErlerGross.neumannA (2 * m) =
      iteratedDeriv (2 * m) (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
        (Nat.factorial (2 * m) : ℝ) := by
  simp [ErlerGross.neumannA]

lemma egReal_hasFPowerSeriesAt :
    HasFPowerSeriesAt
      (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x))
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n => iteratedDeriv n (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
          (n.factorial : ℝ))) 0 := by
  have hf : AnalyticAt ℂ egComplexF (0 : ℂ) := by
    change AnalyticAt ℂ
      (fun w : ℂ => Complex.cos ((2 / 3 : ℂ) * Complex.arctan w)) (0 : ℂ)
    exact analyticAt_cos_two_thirds_arctan_of_norm_lt_one
      (z := (0 : ℂ)) (by norm_num)
  have hr := hf.re_ofReal (x := (0 : ℝ))
  rw [egReal_restriction] at hr
  exact hr.hasFPowerSeriesAt

lemma egComplexF_hasFPowerSeriesAt :
    HasFPowerSeriesAt egComplexF
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => iteratedDeriv n egComplexF 0 / (n.factorial : ℂ))) 0 := by
  have hf : AnalyticAt ℂ egComplexF (0 : ℂ) := by
    change AnalyticAt ℂ
      (fun w : ℂ => Complex.cos ((2 / 3 : ℂ) * Complex.arctan w)) (0 : ℂ)
    exact analyticAt_cos_two_thirds_arctan_of_norm_lt_one
      (z := (0 : ℂ)) (by norm_num)
  exact hf.hasFPowerSeriesAt

lemma egReal_complex_hasFPowerSeriesAt :
    HasFPowerSeriesAt (fun x : ℝ => (egComplexF (x : ℂ)).re)
      (Complex.reCLM.compFormalMultilinearSeries
        (((FormalMultilinearSeries.ofScalars ℂ
          (fun n => iteratedDeriv n egComplexF 0 / (n.factorial : ℂ))).restrictScalars (𝕜 := ℝ)).compContinuousLinearMap
          Complex.ofRealCLM)) 0 := by
  have hc := egComplexF_hasFPowerSeriesAt.restrictScalars (𝕜 := ℝ)
  have hcomp := hc.compContinuousLinearMap (u := Complex.ofRealCLM)
  rcases hcomp with ⟨r, hr⟩
  have hreal := Complex.reCLM.comp_hasFPowerSeriesOnBall hr
  convert hreal.hasFPowerSeriesAt using 1
  · funext x
    simp [Function.comp_def, Complex.reCLM_apply, Complex.ofRealCLM_apply]
  · rfl

set_option maxRecDepth 10000 in
lemma egComplexF_coeff_re_eq (n : ℕ) :
    ((iteratedDeriv n egComplexF 0 / (n.factorial : ℂ)).re) =
      iteratedDeriv n (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
        (n.factorial : ℝ) := by
  have hp_eq :
      (Complex.reCLM.compFormalMultilinearSeries
        (((FormalMultilinearSeries.ofScalars ℂ
          (fun k => iteratedDeriv k egComplexF 0 / (k.factorial : ℂ))).restrictScalars (𝕜 := ℝ)).compContinuousLinearMap
          Complex.ofRealCLM)) =
        (FormalMultilinearSeries.ofScalars ℝ
          (fun k => iteratedDeriv k (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
            (k.factorial : ℝ))) := by
    apply egReal_complex_hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
      egReal_hasFPowerSeriesAt
    exact Filter.Eventually.of_forall (fun x => congrFun egReal_restriction x)
  have hc := congrArg (fun p => p.coeff n) hp_eq
  change
    Complex.reCLM
        ((FormalMultilinearSeries.ofScalars ℂ
          (fun k => iteratedDeriv k egComplexF 0 / (k.factorial : ℂ)) n)
          (fun _ : Fin n => (1 : ℂ))) =
      (FormalMultilinearSeries.ofScalars ℝ
        (fun k => iteratedDeriv k (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
          (k.factorial : ℝ)) n)
        (fun _ : Fin n => (1 : ℝ)) at hc
  simpa only [FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn,
    Finset.prod_const, Finset.card_fin, one_pow, one_mul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_one, Complex.smul_re,
    Complex.reCLM_apply] using hc

lemma egReal_im_restriction :
    (fun x : ℝ => (egComplexF (x : ℂ)).im) = (fun _ : ℝ => 0) := by
  funext x
  calc
    (egComplexF (x : ℂ)).im = ((Real.cos (2 / 3 * Real.arctan x) : ℝ) : ℂ).im :=
      congrArg Complex.im (egComplexF_ofReal x)
    _ = 0 := Complex.ofReal_im _

lemma egReal_im_complex_hasFPowerSeriesAt :
    HasFPowerSeriesAt (fun x : ℝ => (egComplexF (x : ℂ)).im)
      (Complex.imCLM.compFormalMultilinearSeries
        (((FormalMultilinearSeries.ofScalars ℂ
          (fun n => iteratedDeriv n egComplexF 0 / (n.factorial : ℂ))).restrictScalars (𝕜 := ℝ)).compContinuousLinearMap
          Complex.ofRealCLM)) 0 := by
  have hc := egComplexF_hasFPowerSeriesAt.restrictScalars (𝕜 := ℝ)
  have hcomp := hc.compContinuousLinearMap (u := Complex.ofRealCLM)
  rcases hcomp with ⟨r, hr⟩
  have him := Complex.imCLM.comp_hasFPowerSeriesOnBall hr
  convert him.hasFPowerSeriesAt using 1
  · funext x
    simp [Function.comp_def, Complex.imCLM_apply, Complex.ofRealCLM_apply]
  · rfl

set_option maxRecDepth 10000 in
lemma egComplexF_coeff_im_zero (n : ℕ) :
    (iteratedDeriv n egComplexF 0 / (n.factorial : ℂ)).im = 0 := by
  have hzero :
      HasFPowerSeriesAt (fun _ : ℝ => (0 : ℝ))
        (FormalMultilinearSeries.ofScalars ℝ (fun _ => (0 : ℝ))) 0 := by
    simpa using
      (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0).hasFPowerSeriesAt
  have hp_eq :
      (Complex.imCLM.compFormalMultilinearSeries
        (((FormalMultilinearSeries.ofScalars ℂ
          (fun k => iteratedDeriv k egComplexF 0 / (k.factorial : ℂ))).restrictScalars (𝕜 := ℝ)).compContinuousLinearMap
          Complex.ofRealCLM)) =
        (FormalMultilinearSeries.ofScalars ℝ (fun _ => (0 : ℝ))) := by
    apply egReal_im_complex_hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hzero
    exact Filter.Eventually.of_forall (fun x => congrFun egReal_im_restriction x)
  have hc := congrArg (fun p => p.coeff n) hp_eq
  change
    Complex.imCLM
        ((FormalMultilinearSeries.ofScalars ℂ
          (fun k => iteratedDeriv k egComplexF 0 / (k.factorial : ℂ)) n)
          (fun _ : Fin n => (1 : ℂ))) =
      (FormalMultilinearSeries.ofScalars ℝ (fun _ => (0 : ℝ)) n)
        (fun _ : Fin n => (1 : ℝ)) at hc
  simpa only [FormalMultilinearSeries.ofScalars,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn,
    Finset.prod_const, Finset.card_fin, one_pow, one_mul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_one,
    Complex.smul_im, Complex.imCLM_apply] using hc

lemma egComplexF_coeff_eq_ofReal (n : ℕ) :
    iteratedDeriv n egComplexF 0 / (n.factorial : ℂ) =
      (iteratedDeriv n (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
        (n.factorial : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa using egComplexF_coeff_re_eq n
  · rw [egComplexF_coeff_im_zero n]
    simp

lemma complex_arctan_mul_I {t : ℝ} (ht : t ∈ Set.Ioo (-1) 1) :
    Complex.arctan ((t : ℂ) * Complex.I) = (Real.artanh t : ℂ) * Complex.I := by
  have hpos1 : 0 < 1 + t := by linarith [ht.1]
  have hpos2 : 0 < 1 - t := by linarith [ht.2]
  have hposratio : 0 < (1 - t) / (1 + t) := div_pos hpos2 hpos1
  have hratio :
      (1 + ((t : ℂ) * Complex.I) * Complex.I) /
          (1 - ((t : ℂ) * Complex.I) * Complex.I) =
        (((1 - t) / (1 + t) : ℝ) : ℂ) := by
    have hnum : 1 + ((t : ℂ) * Complex.I) * Complex.I = ((1 - t : ℝ) : ℂ) := by
      push_cast
      rw [mul_assoc, Complex.I_mul_I]
      ring
    have hden : 1 - ((t : ℂ) * Complex.I) * Complex.I = ((1 + t : ℝ) : ℂ) := by
      push_cast
      rw [mul_assoc, Complex.I_mul_I]
      ring
    rw [hnum, hden, Complex.ofReal_div]
  rw [Complex.arctan, hratio, ← Complex.ofReal_log (le_of_lt hposratio)]
  have hart : Real.artanh t =
      1 / 2 * Real.log ((1 + t) / (1 - t)) :=
    Real.artanh_eq_half_log (by constructor <;> linarith [ht.1, ht.2])
  rw [hart]
  have hlog : Real.log ((1 - t) / (1 + t)) =
      -Real.log ((1 + t) / (1 - t)) := by
    rw [show (1 - t) / (1 + t) = ((1 + t) / (1 - t))⁻¹ by field_simp]
    exact Real.log_inv _
  rw [hlog]
  push_cast
  ring

lemma egComplexF_I_mul_re {t : ℝ} (ht : t ∈ Set.Ioo (-1) 1) :
    (egComplexF ((t : ℂ) * Complex.I)).re =
      Real.cosh (2 / 3 * Real.artanh t) := by
  rw [egComplexF, complex_arctan_mul_I ht]
  have harg :
      (2 / 3 : ℂ) * ((Real.artanh t : ℂ) * Complex.I) =
        ((2 / 3 * Real.artanh t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cos_mul_I, Complex.cosh_ofReal_re]

lemma hasSum_re_taylor_even {a : ℕ → ℝ} {t g : ℝ}
    (h : HasSum (fun n : ℕ => ((a n : ℂ) * ((t : ℂ) * Complex.I) ^ n).re) g) :
    HasSum (fun m : ℕ => a (2 * m) * (-1 : ℝ)^m * t^(2 * m)) g := by
  replace hs := (Nat.divModEquiv 2).symm.hasSum_iff.mpr h
  dsimp [Function.comp_def] at hs
  refine hs.prod_fiberwise (fun k => ?_)
  convert! hasSum_fintype (_ : Fin 2 → ℝ) using 1
  rw [Fin.sum_univ_two]
  rw [Nat.divModEquiv_symm_apply, Nat.divModEquiv_symm_apply]
  simp only [Fin.val_zero, Fin.val_one, add_zero]
  rw [show k * 2 = 2 * k by ring]
  have hevenpow : ((t : ℂ) * Complex.I) ^ (2 * k) =
      ((-t ^ 2 : ℝ) ^ k : ℂ) := by
    rw [pow_mul, mul_pow, Complex.I_sq]
    push_cast
    ring
  have hevenpow' : ((t : ℂ) * Complex.I) ^ (2 * k) =
      (((-1 : ℝ) ^ k * t ^ (2 * k) : ℝ) : ℂ) := by
    rw [hevenpow]
    norm_cast
    norm_num [Int.cast_pow, Int.cast_negSucc]
    rw [neg_pow, ← pow_mul]
  have hoddpow : ((t : ℂ) * Complex.I) ^ (2 * k + 1) =
      (((-1 : ℝ) ^ k * t ^ (2 * k + 1) : ℝ) : ℂ) * Complex.I := by
    rw [show 2 * k + 1 = (2 * k) + 1 by ring, pow_succ, hevenpow']
    push_cast
    ring
  rw [hevenpow', hoddpow]
  have hevenre :
      (((a (2 * k) : ℂ) * (((-1 : ℝ) ^ k * t ^ (2 * k) : ℝ) : ℂ)).re) =
        a (2 * k) * ((-1 : ℝ) ^ k * t ^ (2 * k)) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hoddre :
      (((a (2 * k + 1) : ℂ) *
        (((( -1 : ℝ) ^ k * t ^ (2 * k + 1) : ℝ) : ℂ) * Complex.I)).re) = 0 := by
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.mul_re]
    rw [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hevenre, hoddre]
  ring

lemma eg_cosh_hasSum {t : ℝ} (ht : t ∈ Set.Ioo (-1) 1) :
    HasSum
      (fun m : ℕ =>
        (iteratedDeriv (2 * m) (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
          (Nat.factorial (2 * m) : ℝ)) * (-1 : ℝ)^m * t^(2 * m))
      (Real.cosh (2 / 3 * Real.artanh t)) := by
  have ht0 : ‖((t : ℂ) * Complex.I)‖ < 1 := by
    have hnorm : ‖((t : ℂ) * Complex.I)‖ = |t| := by simp [norm_mul]
    rw [hnorm]
    exact abs_lt.mpr ⟨ht.1, ht.2⟩
  have htaylor := egComplexF_hasSum_taylor (w := (t : ℂ) * Complex.I) ht0
  have hmap := htaylor.map Complex.reCLM Complex.reCLM.continuous
  have hmap' :
      HasSum (fun n : ℕ =>
        (((iteratedDeriv n (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
          (Nat.factorial n : ℝ) : ℝ) : ℂ) *
          ((t : ℂ) * Complex.I)^n).re)
        (egComplexF ((t : ℂ) * Complex.I)).re := by
    refine hmap.congr_fun ?_
    intro n
    have hcoef :
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n egComplexF 0 =
          ((iteratedDeriv n (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
            (Nat.factorial n : ℝ) : ℝ) : ℂ) := by
      calc
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n egComplexF 0 =
            iteratedDeriv n egComplexF 0 / (n.factorial : ℂ) := by ring
        _ = _ := by
          rw [egComplexF_coeff_eq_ofReal n]
          norm_cast
    simp only [Function.comp_apply, Complex.reCLM_apply]
    rw [hcoef]
  rw [egComplexF_I_mul_re ht] at hmap'
  exact hasSum_re_taylor_even hmap'

lemma eg_cosh_hasSum_neumannA {t : ℝ} (ht : t ∈ Set.Ioo (-1) 1) :
    HasSum (fun m : ℕ => ErlerGross.neumannA (2 * m) * (-1 : ℝ)^m * t^(2 * m))
      (Real.cosh (2 / 3 * Real.artanh t)) := by
  simpa only [neumannA_even_eq] using eg_cosh_hasSum ht

lemma eg_divided_cosh_hasSum {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasSum
      (fun m : ℕ => ErlerGross.neumannA (2 * (m + 1)) *
        (-1 : ℝ)^(m + 1) * t^(2 * m + 1))
      ((Real.cosh (2 / 3 * Real.artanh t) - 1) / t) := by
  have hA0 : ErlerGross.neumannA 0 = 1 := by
    simp [ErlerGross.neumannA]
  have htail := (hasSum_nat_add_iff' 1).mpr
    (eg_cosh_hasSum_neumannA (show t ∈ Set.Ioo (-1) 1 by constructor <;> linarith))
  have htail' :
      HasSum (fun n : ℕ => ErlerGross.neumannA (2 * (n + 1)) *
        (-1 : ℝ)^(n + 1) * t^(2 * (n + 1)))
        (Real.cosh (2 / 3 * Real.artanh t) - 1) := by
    simpa [hA0] using htail
  have hdiv := htail'.div_const t
  refine hdiv.congr_fun ?_
  intro m
  field_simp [ne_of_gt ht0]
  ring

open Real Filter Topology MeasureTheory

lemma intervalIntegral_norm_pow_term {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖a * t ^ (2 * n + 1)‖) =
      a / (2 * (n + 1 : ℕ)) := by
  have hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ a * t ^ (2 * n + 1) := by
    intro t ht
    exact mul_nonneg ha (pow_nonneg ht.1 _)
  have heq : Set.EqOn
      (fun t : ℝ => ‖a * t ^ (2 * n + 1)‖)
      (fun t : ℝ => a * t ^ (2 * n + 1)) (Set.uIcc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le] using ht
    change ‖a * t ^ (2 * n + 1)‖ = a * t ^ (2 * n + 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht')]
  rw [intervalIntegral.integral_congr heq]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

lemma hasSum_integral_of_pointwise_hasSum
    {μ : Measure ℝ} {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hfi : ∀ n, Integrable (f n) μ)
    (hfn : Summable (fun n => ∫ x, ‖f n x‖ ∂μ))
    (hpoint : ∀ᵐ x ∂μ, HasSum (fun n => f n x) (F x)) :
    HasSum (fun n => ∫ x, f n x ∂μ) (∫ x, F x ∂μ) := by
  have hsum := hasSum_integral_of_summable_integral_norm hfi hfn
  have hF : (∫ x, (∑' n, f n x) ∂μ) = ∫ x, F x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hpoint] with x hx
    exact hx.tsum_eq
  rw [hF] at hsum
  exact hsum

lemma weighted_integral_bridge
    {a : ℕ → ℝ} {F : ℝ → ℝ}
    (ha : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => a m / (2 * (m + 1 : ℕ))))
    (hfi : ∀ m : ℕ,
      Integrable (fun t : ℝ => a m * t ^ (2 * m + 1))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      HasSum (fun m : ℕ => a m * t ^ (2 * m + 1)) (F t)) :
    HasSum (fun m : ℕ => a m / (2 * (m + 1 : ℕ)))
      (∫ t in (0 : ℝ)..1, F t) := by
  let μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hnorm : ∀ m : ℕ,
      (∫ t, ‖a m * t ^ (2 * m + 1)‖ ∂μ) =
        a m / (2 * (m + 1 : ℕ)) := by
    intro m
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact intervalIntegral_norm_pow_term (ha m) m
  have hsum_norm : Summable (fun m : ℕ =>
      ∫ t, ‖a m * t ^ (2 * m + 1)‖ ∂μ) := by
    exact hs.congr (fun m => (hnorm m).symm)
  have hpoint' := hpoint
  have hsum := hasSum_integral_of_pointwise_hasSum hfi hsum_norm hpoint'
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hsum
  refine hsum.congr_fun ?_
  intro m
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

open ErlerGross

lemma eg_mode_weighted_integral_reduction
    (hpos : ∀ m : ℕ, 0 ≤ ErlerGross.neumannA (2 * (m + 1)) * (-1 : ℝ)^(m + 1))
    (hs : Summable (fun m : ℕ =>
      (ErlerGross.neumannA (2 * (m + 1)) * (-1 : ℝ)^(m + 1)) /
        (2 * (m + 1 : ℕ)))) :
    HasSum (fun m : ℕ =>
      (ErlerGross.neumannA (2 * (m + 1)) * (-1 : ℝ)^(m + 1)) /
        (2 * (m + 1 : ℕ)))
      (∫ t in (0 : ℝ)..1,
        (Real.cosh (2 / 3 * Real.artanh t) - 1) / t) := by
  apply weighted_integral_bridge hpos hs
  · intro m
    have hc : Continuous (fun t : ℝ =>
        (ErlerGross.neumannA (2 * (m + 1)) * (-1 : ℝ)^(m + 1)) * t^(2*m+1)) := by
      fun_prop
    exact ((hc.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self).integrable
  · have hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), t ≠ 1 := by
      refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with x hx
      exact ne_of_lt hx.2
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with t ht htn
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 htn
    exact eg_divided_cosh_hasSum ht0 ht1

lemma mode_term_eq_neumann_generating (m : ℕ) (hm : 0 < m) :
    3 * ErlerGross.neumannMEven m * ErlerGross.betaVec (2 * m) =
      - ((-1 : ℝ)^m * ErlerGross.neumannA (2 * m) / m) := by
  rw [ErlerGross.neumannMEven, ErlerGross.betaVec]
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [hcast]
  have hcos : Real.cos (2 * (m : ℝ) * Real.pi / 2) = (-1 : ℝ)^m := by
    rw [show 2 * (m : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi by ring]
    exact Real.cos_nat_mul_pi m
  rw [hcos]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : Real.sqrt (2 * (m : ℝ)) ^ 2 = 2 * (m : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_ne : Real.sqrt (2 * (m : ℝ)) ≠ 0 := by positivity
  field_simp [hsqrt_ne]
  rw [hsqrt]
  ring

lemma eg_mode_hasSum_of_pos_summable
    (hpos : ∀ m : ℕ, 0 ≤ ErlerGross.neumannA (2 * (m + 1)) * (-1 : ℝ)^(m + 1))
    (hs : Summable (fun m : ℕ =>
      (ErlerGross.neumannA (2 * (m + 1)) * (-1 : ℝ)^(m + 1)) /
        (2 * (m + 1 : ℕ)))) :
    HasSum (fun n : ℕ =>
      3 * ErlerGross.neumannMEven (n + 1) *
        ErlerGross.betaVec (2 * (n + 1)))
      (-2 * (∫ t in (0 : ℝ)..1,
        (Real.cosh (2 / 3 * Real.artanh t) - 1) / t)) := by
  have hw := eg_mode_weighted_integral_reduction hpos hs
  have hm := hw.mul_left (-2 : ℝ)
  refine hm.congr_fun ?_
  intro n
  rw [mode_term_eq_neumann_generating (n + 1) (by omega)]
  field_simp
/- END INLINE ErlerGross_weighted_reduction.lean -/

/- BEGIN INLINE eg_recurrence3.lean -/
open Real

def egf (x : ℝ) : ℝ := Real.cos (2 / 3 * Real.arctan x)

def egq (x : ℝ) : ℝ := Real.sin (2 / 3 * Real.arctan x) / (1 + x^2)

lemma egf_deriv (x : ℝ) : deriv egf x = -(2 / 3 : ℝ) * egq x := by
  have ha : HasDerivAt (fun y : ℝ => (2 / 3 : ℝ) * Real.arctan y)
      ((2 / 3 : ℝ) * (1 / (1 + x^2))) x := by
    convert (Real.hasDerivAt_arctan x).const_mul (2 / 3 : ℝ) using 1 <;> ring
  have hc := (Real.hasDerivAt_cos (2 / 3 * Real.arctan x)).comp x ha
  change deriv (fun y : ℝ => Real.cos (2 / 3 * Real.arctan y)) x = _
  calc
    _ = -Real.sin (2 / 3 * Real.arctan x) * ((2 / 3 : ℝ) * (1 / (1 + x^2))) := by
      simpa only [Function.comp_def] using hc.deriv
    _ = -(2 / 3 : ℝ) * egq x := by
      dsimp [egq]
      ring

lemma egf_second (x : ℝ) : deriv (deriv egf) x =
    (-(4 / 9 : ℝ) * Real.cos (2 / 3 * Real.arctan x) +
      (4 / 3 : ℝ) * x * Real.sin (2 / 3 * Real.arctan x)) / (1 + x^2)^2 := by
  have hderivFun : deriv egf = fun y => -(2 / 3 : ℝ) * egq y := by
    funext y
    exact egf_deriv y
  rw [hderivFun]
  have ha : HasDerivAt (fun y : ℝ => (2 / 3 : ℝ) * Real.arctan y)
      ((2 / 3 : ℝ) * (1 / (1 + x^2))) x := by
    convert (Real.hasDerivAt_arctan x).const_mul (2 / 3 : ℝ) using 1 <;> ring
  have hsin := (Real.hasDerivAt_sin (2 / 3 * Real.arctan x)).comp x ha
  have hpow : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    simpa [pow_one] using (hasDerivAt_pow 2 x)
  have hden : HasDerivAt (fun y : ℝ => 1 + y^2) (2*x) x := by
    simpa using hpow.const_add (1 : ℝ)
  have hquot := hsin.div hden (by positivity : (1 + x^2 : ℝ) ≠ 0)
  have hscaled := hquot.const_mul (-(2/3 : ℝ))
  have h := hscaled.deriv
  dsimp [egq] at h
  change deriv (fun y : ℝ => -(2 / 3 : ℝ) *
    (Real.sin (2 / 3 * Real.arctan y) / (1 + y^2))) x = _
  rw [h]
  field_simp
  ring

lemma egf_ode (x : ℝ) :
    (1+x^2)^2 * deriv (deriv egf) x + 2*x*(1+x^2)*deriv egf x +
      (4/9:ℝ)*egf x = 0 := by
  rw [egf_second, egf_deriv]
  dsimp [egf, egq]
  field_simp
  ring

lemma egf_contDiff : ContDiff ℝ ⊤ egf := by
  have harg : ContDiff ℝ ⊤ (fun x : ℝ => (2 / 3 : ℝ) * Real.arctan x) := by
    simpa using
      ((contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (2 / 3 : ℝ))).mul
        (Real.contDiff_arctan (n := ⊤)))
  change ContDiff ℝ ⊤ (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x))
  simpa only [Function.comp_def] using (Real.contDiff_cos (n := ⊤)).comp harg


lemma poly_smooth : ContDiff ℝ ⊤ (fun x : ℝ => (1 + x ^ 2) ^ 2) := by
  have hpow2 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 2) := by
    simpa using (contDiff_id (𝕜 := ℝ) (n := ⊤)).pow 2
  have hpow4 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 4) := by
    simpa using (contDiff_id (𝕜 := ℝ) (n := ⊤)).pow 4
  have hscaled : ContDiff ℝ ⊤ (fun x : ℝ => (2 : ℝ) * x ^ 2) := by
    simpa using
      ((contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (2 : ℝ))).mul hpow2)
  have hsum : ContDiff ℝ ⊤ (fun x : ℝ => 1 + 2 * x ^ 2) := by
    simpa using (contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (1 : ℝ))).add hscaled
  have hall : ContDiff ℝ ⊤ (fun x : ℝ => (1 + 2 * x ^ 2) + x ^ 4) := by
    simpa using hsum.add hpow4
  convert hall using 1 <;> ext x <;> ring

lemma poly_deriv_zero (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => (1 + x ^ 2) ^ 2) 0 =
      (if k = 0 then 1 else 0) +
      (if k = 2 then 4 else 0) +
      (if k = 4 then 24 else 0) := by
  have hpow2 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 2) := by
    simpa using (contDiff_id (𝕜 := ℝ) (n := ⊤)).pow 2
  have hpow4 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 4) := by
    simpa using (contDiff_id (𝕜 := ℝ) (n := ⊤)).pow 4
  have hscaled : ContDiff ℝ ⊤ (fun x : ℝ => (2 : ℝ) * x ^ 2) := by
    simpa using
      ((contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (2 : ℝ))).mul hpow2)
  have hsum : ContDiff ℝ ⊤ (fun x : ℝ => 1 + 2 * x ^ 2) := by
    simpa using (contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (1 : ℝ))).add hscaled
  have hall : ContDiff ℝ ⊤ (fun x : ℝ => (1 + 2 * x ^ 2) + x ^ 4) := by
    simpa using hsum.add hpow4
  have hfun : (fun x : ℝ => (1 + x ^ 2) ^ 2) =
      (fun x : ℝ => (1 + 2 * x ^ 2) + x ^ 4) := by
    funext x; ring
  rw [hfun]
  have hfun2 : (fun x : ℝ => (1 + 2 * x ^ 2) + x ^ 4) =
      (fun x : ℝ => 1 + 2 * x ^ 2) + (fun x : ℝ => x ^ 4) := by
    funext x; rfl
  rw [hfun2]
  rw [iteratedDeriv_add (hsum.contDiffAt.of_le (by simp))
      (hpow4.contDiffAt.of_le (by simp))]
  have hfun1 : (fun x : ℝ => 1 + 2 * x ^ 2) =
      (fun x : ℝ => 1) + (fun x : ℝ => (2 : ℝ) * x ^ 2) := by
    funext x; rfl
  rw [hfun1]
  have hc : ContDiffAt ℝ (k : ℕ∞) (fun _ : ℝ => (1 : ℝ)) 0 :=
    contDiffAt_const
  have hs_at : ContDiffAt ℝ (k : ℕ∞) (fun x : ℝ => (2 : ℝ) * x ^ 2) 0 :=
    hscaled.contDiffAt.of_le (by simp)
  rw [iteratedDeriv_add hc hs_at]
  rw [iteratedDeriv_const, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero, iteratedDeriv_fun_pow_zero]
  norm_num

lemma poly_odd_deriv_zero (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => 2 * x * (1 + x ^ 2)) 0 =
      (if k = 1 then 2 else 0) +
      (if k = 3 then 12 else 0) := by
  have hpow1 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 1) := by
    simpa using (contDiff_id (𝕜 := ℝ) (n := ⊤)).pow 1
  have hpow3 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 3) := by
    simpa using (contDiff_id (𝕜 := ℝ) (n := ⊤)).pow 3
  have hscaled1 : ContDiff ℝ ⊤ (fun x : ℝ => (2 : ℝ) * x ^ 1) := by
    simpa using
      ((contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (2 : ℝ))).mul hpow1)
  have hscaled3 : ContDiff ℝ ⊤ (fun x : ℝ => (2 : ℝ) * x ^ 3) := by
    simpa using
      ((contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (2 : ℝ))).mul hpow3)
  have hall : ContDiff ℝ ⊤ (fun x : ℝ => (2 : ℝ) * x ^ 1 + 2 * x ^ 3) := by
    simpa using hscaled1.add hscaled3
  have hfun : (fun x : ℝ => 2 * x * (1 + x ^ 2)) =
      (fun x : ℝ => 2 * x ^ 1 + 2 * x ^ 3) := by
    funext x; ring
  rw [hfun]
  have hfun2 : (fun x : ℝ => (2 : ℝ) * x ^ 1 + 2 * x ^ 3) =
      (fun x : ℝ => (2 : ℝ) * x ^ 1) + (fun x : ℝ => (2 : ℝ) * x ^ 3) := by
    funext x; rfl
  rw [hfun2]
  have h1 : ContDiffAt ℝ (k : ℕ∞) (fun x : ℝ => (2 : ℝ) * x ^ 1) 0 :=
    hscaled1.contDiffAt.of_le (by simp)
  have h3 : ContDiffAt ℝ (k : ℕ∞) (fun x : ℝ => (2 : ℝ) * x ^ 3) 0 :=
    hscaled3.contDiffAt.of_le (by simp)
  rw [iteratedDeriv_add h1 h3,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero, iteratedDeriv_fun_pow_zero]
  norm_num

lemma sum_single (k r : ℕ) (c : ℝ) (A : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * (if i = r then c else 0) * A (k - i) =
      (k.choose r : ℝ) * c * A (k - r) := by
  by_cases h : r ≤ k
  · have hr : r ∈ Finset.range (k + 1) := by simp [h]
    rw [Finset.sum_eq_single r]
    · simp
    · intro b hb hbr
      simp [hbr]
    · intro hrange
      exact False.elim (hrange hr)
  · have hlt : k < r := Nat.lt_of_not_ge h
    have hz : k.choose r = 0 := Nat.choose_eq_zero_of_lt hlt
    simp [hz]

lemma sum_three (k : ℕ) (A : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) *
        ((if i = 0 then 1 else 0) + (if i = 2 then 4 else 0) +
          (if i = 4 then 24 else 0)) * A (k - i) =
      A k + (k.choose 2 : ℝ) * 4 * A (k - 2) +
        (k.choose 4 : ℝ) * 24 * A (k - 4) := by
  calc
    _ = ∑ i ∈ Finset.range (k + 1),
        ((k.choose i : ℝ) * (if i = 0 then 1 else 0) * A (k - i) +
          (k.choose i : ℝ) * (if i = 2 then 4 else 0) * A (k - i) +
          (k.choose i : ℝ) * (if i = 4 then 24 else 0) * A (k - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (if i = 0 then 1 else 0) * A (k - i)) +
        (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (if i = 2 then 4 else 0) * A (k - i)) +
        (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (if i = 4 then 24 else 0) * A (k - i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by rw [sum_single, sum_single, sum_single]; simp

lemma sum_two (k : ℕ) (A : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) *
        ((if i = 1 then 2 else 0) + (if i = 3 then 12 else 0)) * A (k - i) =
      (k.choose 1 : ℝ) * 2 * A (k - 1) +
        (k.choose 3 : ℝ) * 12 * A (k - 3) := by
  calc
    _ = ∑ i ∈ Finset.range (k + 1),
        ((k.choose i : ℝ) * (if i = 1 then 2 else 0) * A (k - i) +
          (k.choose i : ℝ) * (if i = 3 then 12 else 0) * A (k - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (if i = 1 then 2 else 0) * A (k - i)) +
        (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (if i = 3 then 12 else 0) * A (k - i)) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by rw [sum_single, sum_single]

lemma poly_odd_smooth : ContDiff ℝ ⊤ (fun x : ℝ => 2 * x * (1 + x ^ 2)) := by
  have hpow1 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 1) := by
    simpa using (contDiff_id (𝕜 := ℝ) (n := ⊤)).pow 1
  have hpow3 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 3) := by
    simpa using (contDiff_id (𝕜 := ℝ) (n := ⊤)).pow 3
  have hscaled1 : ContDiff ℝ ⊤ (fun x : ℝ => (2 : ℝ) * x ^ 1) := by
    simpa using
      ((contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (2 : ℝ))).mul hpow1)
  have hscaled3 : ContDiff ℝ ⊤ (fun x : ℝ => (2 : ℝ) * x ^ 3) := by
    simpa using
      ((contDiff_const (𝕜 := ℝ) (n := ⊤) (c := (2 : ℝ))).mul hpow3)
  have hall : ContDiff ℝ ⊤ (fun x : ℝ => (2 : ℝ) * x ^ 1 + 2 * x ^ 3) := by
    simpa using hscaled1.add hscaled3
  convert hall using 1 <;> ext x <;> ring

lemma ode_iterated (k : ℕ) :
    iteratedDeriv k
        (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x +
          2 * x * (1 + x ^ 2) * deriv egf x +
          (4 / 9 : ℝ) * egf x) 0 = 0 := by
  have hfun :
      (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x +
          2 * x * (1 + x ^ 2) * deriv egf x +
          (4 / 9 : ℝ) * egf x) = (fun _ : ℝ => 0) := by
    funext x
    exact egf_ode x
  rw [hfun]
  simp [iteratedDeriv_const]

lemma ode_expanded (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) *
        iteratedDeriv i (fun x : ℝ => (1 + x ^ 2) ^ 2) 0 *
        iteratedDeriv (k - i) (deriv (deriv egf)) 0) +
      (∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) *
          iteratedDeriv i (fun x : ℝ => 2 * x * (1 + x ^ 2)) 0 *
          iteratedDeriv (k - i) (deriv egf) 0) +
      (4 / 9 : ℝ) * iteratedDeriv k egf 0 = 0 := by
  have hP : ContDiffAt ℝ (k : ℕ∞) (fun x : ℝ => (1 + x ^ 2) ^ 2) 0 :=
    poly_smooth.contDiffAt.of_le (by simp)
  have hQ : ContDiffAt ℝ (k : ℕ∞) (fun x : ℝ => 2 * x * (1 + x ^ 2)) 0 :=
    poly_odd_smooth.contDiffAt.of_le (by simp)
  have hf : ContDiffAt ℝ (k : ℕ∞) egf 0 :=
    egf_contDiff.contDiffAt.of_le (by simp)
  have hdf : ContDiffAt ℝ (k : ℕ∞) (deriv egf) 0 := by
    exact egf_contDiff.contDiffAt.derivWithin (m := (k : ℕ∞)) (by simp)
  have hddf : ContDiffAt ℝ (k : ℕ∞) (deriv (deriv egf)) 0 := by
    have h1 : ContDiffAt ℝ ((k + 1 : ℕ) : ℕ∞) (deriv egf) 0 :=
      egf_contDiff.contDiffAt.derivWithin (m := ((k + 1 : ℕ) : ℕ∞)) (by simp)
    exact h1.derivWithin (m := (k : ℕ∞)) (by simp)
  have hPprod := hP.mul hddf
  have hQprod := hQ.mul hdf
  have hC : ContDiffAt ℝ (k : ℕ∞)
      (fun x : ℝ => (4 / 9 : ℝ) * egf x) 0 := by
    simpa [smul_eq_mul] using hf.const_smul (4 / 9 : ℝ)
  have hPQ := hPprod.add hQprod
  have hsumfun :
      (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x +
          2 * x * (1 + x ^ 2) * deriv egf x +
          (4 / 9 : ℝ) * egf x) =
        (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x +
          2 * x * (1 + x ^ 2) * deriv egf x) +
          (fun x : ℝ => (4 / 9 : ℝ) * egf x) := by
    funext x
    rfl
  have hi := ode_iterated k
  rw [hsumfun] at hi
  rw [iteratedDeriv_add hPQ hC] at hi
  have hPQfun :
      (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x +
          2 * x * (1 + x ^ 2) * deriv egf x) =
        (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x) +
          (fun x : ℝ => 2 * x * (1 + x ^ 2) * deriv egf x) := by
    funext x
    rfl
  rw [hPQfun] at hi
  rw [iteratedDeriv_add hPprod hQprod] at hi
  have hPfun :
      (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x) =
        (fun x : ℝ => (1 + x ^ 2) ^ 2) * deriv (deriv egf) := by
    funext x
    rfl
  have hQfun :
      (fun x : ℝ => 2 * x * (1 + x ^ 2) * deriv egf x) =
        (fun x : ℝ => 2 * x * (1 + x ^ 2)) * deriv egf := by
    funext x
    rfl
  rw [hPfun, hQfun] at hi
  rw [iteratedDeriv_mul hP hddf, iteratedDeriv_mul hQ hdf] at hi
  rw [iteratedDeriv_const_mul_field] at hi
  simpa only [Pi.mul_apply] using hi

lemma p_product (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x) 0 =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) *
          iteratedDeriv i (fun x : ℝ => (1 + x ^ 2) ^ 2) 0 *
          iteratedDeriv (k - i) (deriv (deriv egf)) 0 := by
  have hP : ContDiffAt ℝ (k : ℕ∞) (fun x : ℝ => (1 + x ^ 2) ^ 2) 0 :=
    poly_smooth.contDiffAt.of_le (by simp)
  have hddf : ContDiffAt ℝ (k : ℕ∞) (deriv (deriv egf)) 0 := by
    have h1 : ContDiffAt ℝ ((k + 1 : ℕ) : ℕ∞) (deriv egf) 0 :=
      egf_contDiff.contDiffAt.derivWithin (m := ((k + 1 : ℕ) : ℕ∞)) (by simp)
    exact h1.derivWithin (m := (k : ℕ∞)) (by simp)
  have h := iteratedDeriv_mul (f := (fun x : ℝ => (1 + x ^ 2) ^ 2))
      (g := deriv (deriv egf)) hP hddf
  have hfun : (fun x : ℝ => (1 + x ^ 2) ^ 2 * deriv (deriv egf) x) =
      (fun x : ℝ => (1 + x ^ 2) ^ 2) * deriv (deriv egf) := by
    funext x
    rfl
  rw [hfun]
  exact h

lemma q_product (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => 2 * x * (1 + x ^ 2) * deriv egf x) 0 =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) *
          iteratedDeriv i (fun x : ℝ => 2 * x * (1 + x ^ 2)) 0 *
          iteratedDeriv (k - i) (deriv egf) 0 := by
  have hQ : ContDiffAt ℝ (k : ℕ∞) (fun x : ℝ => 2 * x * (1 + x ^ 2)) 0 :=
    poly_odd_smooth.contDiffAt.of_le (by simp)
  have hdf : ContDiffAt ℝ (k : ℕ∞) (deriv egf) 0 := by
    exact egf_contDiff.contDiffAt.derivWithin (m := (k : ℕ∞)) (by simp)
  have h := iteratedDeriv_mul (f := (fun x : ℝ => 2 * x * (1 + x ^ 2)))
      (g := deriv egf) hQ hdf
  have hfun : (fun x : ℝ => 2 * x * (1 + x ^ 2) * deriv egf x) =
      (fun x : ℝ => 2 * x * (1 + x ^ 2)) * deriv egf := by
    funext x
    rfl
  rw [hfun]
  exact h

lemma shift1 (m : ℕ) :
    iteratedDeriv m (deriv egf) 0 = iteratedDeriv (m + 1) egf 0 := by
  have h := congrFun (iteratedDeriv_succ' (n := m) (f := egf)) 0
  exact h.symm

lemma shift2 (m : ℕ) :
    iteratedDeriv m (deriv (deriv egf)) 0 = iteratedDeriv (m + 2) egf 0 := by
  have h1 := congrFun (iteratedDeriv_succ' (n := m) (f := deriv egf)) 0
  have h2 := congrFun (iteratedDeriv_succ' (n := m + 1) (f := egf)) 0
  rw [← h1, ← h2]

lemma p_shift4 (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (A : ℕ → ℝ) :
    (k.choose 4 : ℝ) * c * A ((k - 4) + 2) =
      (k.choose 4 : ℝ) * c * A (k - 2) := by
  by_cases h4 : 4 ≤ k
  · have heq : (k - 4) + 2 = k - 2 := by omega
    rw [heq]
  · have hlt : k < 4 := Nat.lt_of_not_ge h4
    have hz : k.choose 4 = 0 := Nat.choose_eq_zero_of_lt hlt
    simp [hz]

lemma p_sum (k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) *
        iteratedDeriv i (fun x : ℝ => (1 + x ^ 2) ^ 2) 0 *
        iteratedDeriv (k - i) (deriv (deriv egf)) 0) =
      iteratedDeriv (k + 2) egf 0 +
        (k.choose 2 : ℝ) * 4 * iteratedDeriv k egf 0 +
        (k.choose 4 : ℝ) * 24 * iteratedDeriv (k - 2) egf 0 := by
  rw [← p_product k]
  -- Put the finite polynomial derivative and the two derivative shifts into the sum.
  rw [p_product k]
  simp_rw [poly_deriv_zero, shift2]
  have hs := sum_three k (fun j => iteratedDeriv (j + 2) egf 0)
  rw [hs]
  have h2 : (k - 2) + 2 = k := Nat.sub_add_cancel hk
  rw [h2]
  rw [p_shift4 k hk 24 (fun j => iteratedDeriv j egf 0)]

lemma q_shift3 (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (A : ℕ → ℝ) :
    (k.choose 3 : ℝ) * c * A ((k - 3) + 1) =
      (k.choose 3 : ℝ) * c * A (k - 2) := by
  by_cases h3 : 3 ≤ k
  · have heq : (k - 3) + 1 = k - 2 := by omega
    rw [heq]
  · have hlt : k < 3 := Nat.lt_of_not_ge h3
    have hz : k.choose 3 = 0 := Nat.choose_eq_zero_of_lt hlt
    simp [hz]

lemma q_sum (k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) *
        iteratedDeriv i (fun x : ℝ => 2 * x * (1 + x ^ 2)) 0 *
        iteratedDeriv (k - i) (deriv egf) 0) =
      (k.choose 1 : ℝ) * 2 * iteratedDeriv k egf 0 +
        (k.choose 3 : ℝ) * 12 * iteratedDeriv (k - 2) egf 0 := by
  rw [← q_product k]
  rw [q_product k]
  simp_rw [poly_odd_deriv_zero, shift1]
  have hs := sum_two k (fun j => iteratedDeriv (j + 1) egf 0)
  rw [hs]
  have h1 : (k - 1) + 1 = k := Nat.sub_add_cancel (by omega)
  rw [h1]
  rw [q_shift3 k hk 12 (fun j => iteratedDeriv j egf 0)]

lemma ode_coeff_choose (k : ℕ) (hk : 2 ≤ k) :
    iteratedDeriv (k + 2) egf 0 +
        (4 * (k.choose 2 : ℝ) + 2 * (k.choose 1 : ℝ) + (4 / 9 : ℝ)) *
          iteratedDeriv k egf 0 +
        (24 * (k.choose 4 : ℝ) + 12 * (k.choose 3 : ℝ)) *
          iteratedDeriv (k - 2) egf 0 = 0 := by
  have h := ode_expanded k
  rw [p_sum k hk, q_sum k hk] at h
  linarith


lemma choose2_real (k : ℕ) :
    (k.choose 2 : ℝ) * 2 = (k : ℝ) * (k - 1 : ℕ) := by
  have h := Nat.choose_succ_right_eq k 1
  -- h : choose (1+1) * (1+1) = choose 1 * (k-1)
  norm_num at h
  exact_mod_cast h

lemma choose3_real (k : ℕ) :
    (k.choose 3 : ℝ) * 3 = (k.choose 2 : ℝ) * (k - 2 : ℕ) := by
  have h := Nat.choose_succ_right_eq k 2
  norm_num at h
  exact_mod_cast h

lemma choose4_real (k : ℕ) :
    (k.choose 4 : ℝ) * 4 = (k.choose 3 : ℝ) * (k - 3 : ℕ) := by
  have h := Nat.choose_succ_right_eq k 3
  norm_num at h
  exact_mod_cast h

lemma coeff_mid (k : ℕ) :
    4 * (k.choose 2 : ℝ) + 2 * (k.choose 1 : ℝ) + (4 / 9 : ℝ) =
      2 * (k : ℝ) ^ 2 + (4 / 9 : ℝ) := by
  by_cases hk : k = 0
  · simp [hk]
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have h2 := choose2_real k
  have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk1]
    norm_num
  have h1 : (k.choose 1 : ℝ) = (k : ℝ) := by simp [Nat.choose_one_right]
  rw [hsub] at h2
  rw [h1]
  nlinarith

lemma coeff_last (k : ℕ) (hk : 2 ≤ k) :
    24 * (k.choose 4 : ℝ) + 12 * (k.choose 3 : ℝ) =
      (k : ℝ) * (k - 1 : ℕ) ^ 2 * (k - 2 : ℕ) := by
  by_cases hk3 : 3 ≤ k
  · have hk1 : 1 ≤ k := by omega
    have hk2 : 2 ≤ k := hk
    have h2 := choose2_real k
    have h3 := choose3_real k
    have h4 := choose4_real k
    have hs1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk1]
      norm_num
    have hs2 : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub hk2]
      norm_num
    have hs3 : ((k - 3 : ℕ) : ℝ) = (k : ℝ) - 3 := by
      rw [Nat.cast_sub hk3]
      norm_num
    rw [hs1] at h2
    rw [hs2] at h3
    rw [hs3] at h4
    calc
      24 * (k.choose 4 : ℝ) + 12 * (k.choose 3 : ℝ) =
          6 * ((k.choose 4 : ℝ) * 4) + 12 * (k.choose 3 : ℝ) := by ring
      _ = 6 * ((k.choose 3 : ℝ) * ((k : ℝ) - 3)) +
          12 * (k.choose 3 : ℝ) := by rw [h4]
      _ = 6 * (k.choose 3 : ℝ) * ((k : ℝ) - 1) := by ring
      _ = 2 * ((k.choose 3 : ℝ) * 3) * ((k : ℝ) - 1) := by ring
      _ = 2 * ((k.choose 2 : ℝ) * ((k : ℝ) - 2)) * ((k : ℝ) - 1) := by rw [h3]
      _ = ((k.choose 2 : ℝ) * 2) * ((k : ℝ) - 2) * ((k : ℝ) - 1) := by ring
      _ = ((k : ℝ) * ((k : ℝ) - 1)) * ((k : ℝ) - 2) * ((k : ℝ) - 1) := by rw [h2]
      _ = (k : ℝ) * (k - 1 : ℕ) ^ 2 * (k - 2 : ℕ) := by
        rw [hs1, hs2]
        ring
  · have hk2 : k = 2 := by omega
    subst k
    norm_num [Nat.choose]

lemma ode_coeff_nat (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n + 2) egf 0 +
        (8 * (n : ℝ) ^ 2 + (4 / 9 : ℝ)) * iteratedDeriv (2 * n) egf 0 +
        (4 * (n : ℝ) * (n - 1 : ℕ) * (2 * (n : ℝ) - 1) ^ 2) *
          iteratedDeriv (2 * n - 2) egf 0 = 0 := by
  have hk : 2 ≤ 2 * n := by omega
  have h := ode_coeff_choose (2 * n) hk
  rw [coeff_mid, coeff_last (2 * n) hk] at h
  have hsub : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hsub2 : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hsub, hsub2] at h
  have hsubn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hsubn]
  convert h using 1
  norm_num [Nat.cast_mul]
  ring

noncomputable def egB (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n *
    (iteratedDeriv (2 * n) egf 0 / ((2 * n).factorial : ℝ))

lemma mode_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℝ) * (2 * n + 1) * egB (n + 1) -
        (4 * (n : ℝ) ^ 2 + 2 / 9) * egB n +
        (n - 1 : ℕ) * (2 * n - 1) * egB (n - 1) = 0 := by
  have h := ode_coeff_nat n hn
  simp only [egB]
  have hidxplus : 2 * (n + 1) = 2 * n + 2 := by omega
  have hidxminus : 2 * (n - 1) = 2 * n - 2 := by omega
  rw [hidxplus, hidxminus]
  have hfactplus : (2 * n + 2).factorial =
      (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ,
      show 2 * n + 1 = (2 * n) + 1 by omega,
      Nat.factorial_succ]
    ring
  have hfactminus : (2 * n).factorial =
      (2 * n) * (2 * n - 1) * (2 * n - 2).factorial := by
    calc
      (2 * n).factorial = (2 * n) * (2 * n - 1).factorial := by
        have heq : (2 * n - 1) + 1 = 2 * n := by omega
        calc
          (2 * n).factorial = ((2 * n - 1) + 1).factorial := by
            exact congrArg Nat.factorial heq.symm
          _ = ((2 * n - 1) + 1) * (2 * n - 1).factorial := by
            rw [Nat.factorial_succ]
          _ = (2 * n) * (2 * n - 1).factorial := by rw [heq]
      _ = (2 * n) * ((2 * n - 1) * (2 * n - 2).factorial) := by
        congr 1
        have heq : (2 * n - 2) + 1 = 2 * n - 1 := by omega
        calc
          (2 * n - 1).factorial = ((2 * n - 2) + 1).factorial := by
            exact congrArg Nat.factorial heq.symm
          _ = ((2 * n - 2) + 1) * (2 * n - 2).factorial := by
            rw [Nat.factorial_succ]
          _ = (2 * n - 1) * (2 * n - 2).factorial := by rw [heq]
      _ = (2 * n) * (2 * n - 1) * (2 * n - 2).factorial := by ring
  rw [hfactplus, hfactminus]
  have hsignplus : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by
    rw [pow_succ]
    ring
  have hsignminus : (-1 : ℝ) ^ (n - 1) = -((-1 : ℝ) ^ n) := by
    calc
      (-1 : ℝ) ^ (n - 1) = -((-1 : ℝ) ^ ((n - 1) + 1)) := by
        rw [pow_succ]
        ring
      _ = -((-1 : ℝ) ^ n) := by rw [Nat.sub_add_cancel hn]
  rw [hsignplus, hsignminus]
  have hfactn : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  have hfactnm : ((2 * n - 2).factorial : ℝ) ≠ 0 := by positivity
  have hfactplusR : (((2 * n + 2) * (2 * n + 1) * (2 * n).factorial : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hfactminusR : (((2 * n) * (2 * n - 1) * (2 * n - 2).factorial : ℕ) : ℝ) ≠ 0 := by
    have hp : 0 < (2 * n) * (2 * n - 1) * (2 * n - 2).factorial := by
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.factorial_pos _)
    exact_mod_cast (Nat.ne_of_gt hp)
  have hfullR :
      (↑(((2 * n + 2) * (2 * n + 1) *
          ((2 * n) * (2 * n - 1) * (2 * n - 2).factorial) : ℕ)) : ℝ) ≠ 0 := by
    have hp : 0 < (2 * n + 2) * (2 * n + 1) *
        ((2 * n) * (2 * n - 1) * (2 * n - 2).factorial) := by
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega))
        (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.factorial_pos _))
    exact_mod_cast (Nat.ne_of_gt hp)
  have hsub : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hsub2 : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hsubn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  field_simp [hfactn, hfactnm, hfactplusR, hfactminusR, hfullR]
  norm_num [Nat.cast_mul] at ⊢
  simp only [hsub, hsubn] at ⊢
  have h' := h
  simp only [hsub, hsubn] at h'
  linear_combination
    (-18 * (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) - 1) *
      (2 * (n : ℝ) + 1) * ((2 * n - 2).factorial : ℝ) ^ 2) * h' 
/- END INLINE eg_recurrence3.lean -/

/- BEGIN INLINE RatioBounds.lean -/
open Real Filter Topology


private def L (n : ℕ) : ℝ :=
  (6 * (n : ℝ) - 5) / (6 * (n : ℝ) - 1)

lemma ratio_bounds_of_recurrence
    (b : ℕ → ℝ)
    (hb0 : b 0 = 1)
    (hb1 : b 1 = 2 / 9)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) * b (n + 1)
        - (4 * (n : ℝ) ^ 2 + 2 / 9) * b n
        + ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * b (n - 1) = 0) :
    ∀ n : ℕ, 1 ≤ n →
      0 ≤ b n ∧ L n * b (n - 1) ≤ b n ∧ b n ≤ b (n - 1) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        intro hn
        rw [hb0, hb1]
        norm_num [L]
      · intro hnnext
        have hn1 : 1 ≤ n := by omega
        obtain ⟨hbn, hlow, hupper⟩ := ih hn1
        have hL : 0 < L n := by
          dsimp [L]
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          have hnum : 0 < 6 * (n : ℝ) - 5 := by nlinarith
          have hden : 0 < 6 * (n : ℝ) - 1 := by nlinarith
          positivity
        have hLnext : 0 < L (n + 1) := by
          dsimp [L]
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          have hnum : 0 < 6 * ((n + 1 : ℕ) : ℝ) - 5 := by
            push_cast
            nlinarith
          have hden : 0 < 6 * ((n + 1 : ℕ) : ℝ) - 1 := by
            push_cast
            nlinarith
          positivity
        have hA : 0 < ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) := by positivity
        have hC : 0 ≤ ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          have h2n : 0 < 2 * (n : ℝ) - 1 := by nlinarith
          positivity
        have hcoef :
            L n * (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) * L (n + 1) ≤
              L n * (4 * (n : ℝ) ^ 2 + 2 / 9) -
                ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
          dsimp [L]
          push_cast
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          have hden1 : (6 * (n : ℝ) - 1) ≠ 0 := by nlinarith
          have hden2 : (6 * (n : ℝ) + 5) ≠ 0 := by nlinarith
          have hden3 : (6 * (n : ℝ) - 5) ≠ 0 := by nlinarith
          have hden4 : (6 * ((n + 1 : ℕ) : ℝ) - 1) ≠ 0 := by
            push_cast
            nlinarith
          have hden5 : (6 * ((n + 1 : ℕ) : ℝ) - 5) ≠ 0 := by
            push_cast
            nlinarith
          rw [show 6 * ((n : ℝ) + 1) - 1 = 6 * (n : ℝ) + 5 by ring,
            show 6 * ((n : ℝ) + 1) - 5 = 6 * (n : ℝ) + 1 by ring]
          have hdenpos : 0 < 6 * (n : ℝ) - 1 := by nlinarith
          field_simp [hden1, hden2, hden3, hden4, hden5, ne_of_gt hdenpos]
          ring_nf
          field_simp [ne_of_gt hdenpos]
          nlinarith [sq_nonneg ((n : ℝ) - 1)]
        have hlowmul :
            ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (L n * b (n - 1)) ≤
              ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * b n :=
          mul_le_mul_of_nonneg_left hlow hC
        have hcoefmul := mul_le_mul_of_nonneg_right hcoef hbn
        have hrec' := hrec n hn1
        have hchain :
            L n * (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) *
                (L (n + 1) * b n) ≤
              L n * (4 * (n : ℝ) ^ 2 + 2 / 9) * b n -
                ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (L n * b (n - 1)) := by
          nlinarith [hlowmul, hcoefmul]
        have hrecL :
            L n * (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) * b (n + 1)) =
              L n * (4 * (n : ℝ) ^ 2 + 2 / 9) * b n -
                ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (L n * b (n - 1)) := by
          nlinarith [hrec']
        have hnextlow : L (n + 1) * b n ≤ b (n + 1) := by
          have hLpos : 0 < L n := hL
          have hApos : 0 < ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) := hA
          have hmul :
              L n * (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) *
                  (L (n + 1) * b n) ≤
                L n * (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) * b (n + 1) := by
            nlinarith [hchain, hrecL]
          exact le_of_mul_le_mul_left (by simpa [mul_assoc] using hmul) (mul_pos hLpos hApos)
        have huppermul :
            ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * b n ≤
              ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * b (n - 1) :=
          mul_le_mul_of_nonneg_left hupper hC
        have hBA :
            (4 * (n : ℝ) ^ 2 + 2 / 9) -
                ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) ≤
              ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) := by
          push_cast
          nlinarith
        have hnextupper : b (n + 1) ≤ b n := by
          have hBA_mul := mul_le_mul_of_nonneg_right hBA hbn
          have hApos : 0 < ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) := hA
          have hmul :
              (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) * b (n + 1) ≤
                (((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1)) * b n := by
            nlinarith [hrec', huppermul, hBA_mul]
          exact le_of_mul_le_mul_left hmul hApos
        have hnextnonneg : 0 ≤ b (n + 1) := by
          have : 0 ≤ L (n + 1) * b n := mul_nonneg (le_of_lt hLnext) hbn
          exact this.trans hnextlow
        exact ⟨hnextnonneg, by simpa using hnextlow, by simpa using hnextupper⟩

lemma second_coeff_of_recurrence
    (b : ℕ → ℝ)
    (hb0 : b 0 = 1)
    (hb1 : b 1 = 2 / 9)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) * b (n + 1)
        - (4 * (n : ℝ) ^ 2 + 2 / 9) * b n
        + ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * b (n - 1) = 0) :
    b 2 = 38 / 243 := by
  have h := hrec 1 (by norm_num)
  norm_num [hb0, hb1] at h
  linarith
/- END INLINE RatioBounds.lean -/

/- BEGIN INLINE eg_scalar_h_eval.lean -/

open Real Filter Topology MeasureTheory
open Set

namespace ErlerGrossScratch

lemma scalar_geom (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (∑' n : ℕ, 6 * y ^ (6*n+1) * (1-y)^2) =
      6 * y * (1-y)^2 / (1-y^6) := by
  by_cases hlt : y < 1
  · have hy0 : 0 ≤ y := hy.1
    have hpow : y ^ 6 < (1 : ℝ) := by
      exact pow_lt_one₀ hy0 hlt (by norm_num)
    have hnorm : ‖y ^ 6‖ < (1 : ℝ) := by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpow
    have hg := tsum_geometric_of_norm_lt_one (ξ := y ^ 6) hnorm
    have hscaled : (∑' n : ℕ, (6 * y * (1-y)^2) * (y^6)^n) =
        6 * y * (1-y)^2 / (1-y^6) := by
      rw [tsum_mul_left]
      exact congrArg (fun z : ℝ => (6 * y * (1-y)^2) * z) hg
    have hterm : ∀ n : ℕ,
        (6 * y * (1-y)^2) * (y^6)^n = 6 * y ^ (6*n+1) * (1-y)^2 := by
      intro n
      rw [← pow_mul]
      rw [show 6 * n + 1 = 1 + 6*n by omega, pow_add]
      ring
    rw [show (∑' n : ℕ, 6 * y ^ (6*n+1) * (1-y)^2) =
      ∑' n : ℕ, (6 * y * (1-y)^2) * (y^6)^n by
        apply tsum_congr
        intro n
        exact (hterm n).symm]
    exact hscaled
  · have hyeq : y = 1 := le_antisymm hy.2 (le_of_not_gt hlt)
    simp [hyeq]

lemma scalar_term_integrable (n : ℕ) :
    Integrable (fun y : ℝ => 6 * y ^ (6*n+1) * (1-y)^2)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hc : Continuous (fun y : ℝ => 6 * y ^ (6*n+1) * (1-y)^2) := by
    fun_prop
  exact ((hc.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self).integrable

lemma scalar_term_norm (n : ℕ) :
    (∫ y, ‖6 * y ^ (6*n+1) * (1-y)^2‖
      ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) =
      1 / (((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2))) := by
  have hnonneg : Set.EqOn
      (fun y : ℝ => ‖6 * y ^ (6*n+1) * (1-y)^2‖)
      (fun y : ℝ => 6 * y ^ (6*n+1) * (1-y)^2) (Set.Ioc (0 : ℝ) 1) := by
    intro y hy
    change ‖6 * y ^ (6*n+1) * (1-y)^2‖ = 6 * y ^ (6*n+1) * (1-y)^2
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have hy0 : 0 ≤ y := le_of_lt hy.1
    have hy1 : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
    positivity
  rw [MeasureTheory.integral_congr_ae]
  · rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have heq : (fun y : ℝ => 6 * y ^ (6*n+1) * (1-y)^2) =
        (fun y : ℝ => 6 * (y^(6*n+1) - 2*y^(6*n+2) + y^(6*n+3))) := by
      funext y
      ring
    rw [heq, intervalIntegral.integral_const_mul]
    have hA : IntervalIntegrable (fun y : ℝ => y^(6*n+1)) volume 0 1 :=
      (continuous_pow _).intervalIntegrable 0 1
    have hB : IntervalIntegrable (fun y : ℝ => y^(6*n+2)) volume 0 1 :=
      (continuous_pow _).intervalIntegrable 0 1
    have hC : IntervalIntegrable (fun y : ℝ => y^(6*n+3)) volume 0 1 :=
      (continuous_pow _).intervalIntegrable 0 1
    have h2B : IntervalIntegrable (fun y : ℝ => 2 * y^(6*n+2)) volume 0 1 :=
      hB.const_mul 2
    have hAB : IntervalIntegrable (fun y : ℝ => y^(6*n+1) - 2*y^(6*n+2)) volume 0 1 :=
      hA.sub h2B
    rw [intervalIntegral.integral_add hAB hC]
    rw [intervalIntegral.integral_sub hA h2B]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_pow, integral_pow, integral_pow]
    norm_num
    have h1 : (0 : ℝ) < 2*(n:ℝ)+1 := by positivity
    have h2 : (0 : ℝ) < 3*(n:ℝ)+1 := by positivity
    have h3 : (0 : ℝ) < 3*(n:ℝ)+2 := by positivity
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3]
    ring
  · exact ae_restrict_of_forall_mem measurableSet_Ioc hnonneg

 theorem scalar_rational_integral_eval :
    6 * (∫ y in (0 : ℝ)..1, y * (1-y)^2 / (1-y^6)) =
      Real.log (27 / 16) := by
  have hgs : Summable (fun n : ℕ =>
      1 / (((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2)))) :=
    ErlerGross.B3_cubic_reciprocal_series_closed_form.summable
  have hFint : ∀ n : ℕ,
      Integrable (fun y : ℝ => 6 * y ^ (6*n+1) * (1-y)^2)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro n
    exact scalar_term_integrable n
  have hFsum : Summable (fun n : ℕ =>
      ∫ y, ‖6 * y ^ (6*n+1) * (1-y)^2‖
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    exact hgs.congr (fun n => (scalar_term_norm n).symm)
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (F := fun n : ℕ => fun y : ℝ => 6 * y ^ (6*n+1) * (1-y)^2)
    hFint hFsum
  have hswap' := hswap
  simp_rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hswap'
  have hsum_fun : Set.EqOn
      (fun y : ℝ => ∑' n : ℕ, 6 * y ^ (6*n+1) * (1-y)^2)
      (fun y : ℝ => 6 * y * (1-y)^2 / (1-y^6))
      (Set.uIcc 0 1) := by
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le] using hy
    exact scalar_geom y hy'
  rw [intervalIntegral.integral_congr hsum_fun] at hswap'
  have hterm' (n : ℕ) :
      (∫ y in (0 : ℝ)..1, 6 * y ^ (6*n+1) * (1-y)^2) =
        1 / (((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2))) := by
    have hnonneg : Set.EqOn
        (fun y : ℝ => ‖6 * y ^ (6*n+1) * (1-y)^2‖)
        (fun y : ℝ => 6 * y ^ (6*n+1) * (1-y)^2) (Set.Icc (0 : ℝ) 1) := by
      intro y hy
      change ‖6 * y ^ (6*n+1) * (1-y)^2‖ = 6 * y ^ (6*n+1) * (1-y)^2
      rw [Real.norm_eq_abs, abs_of_nonneg]
      have hy0 : 0 ≤ y := hy.1
      have hy1 : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
      positivity
    have heq : (∫ y in (0 : ℝ)..1, 6 * y ^ (6*n+1) * (1-y)^2) =
        ∫ y in (0 : ℝ)..1, ‖6 * y ^ (6*n+1) * (1-y)^2‖ := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le] using hy
      exact (hnonneg hy').symm
    calc
      (∫ y in (0 : ℝ)..1, 6 * y ^ (6*n+1) * (1-y)^2) =
          ∫ y in (0 : ℝ)..1, ‖6 * y ^ (6*n+1) * (1-y)^2‖ := heq
      _ = ∫ y, ‖6 * y ^ (6*n+1) * (1-y)^2‖
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)
      _ = _ := scalar_term_norm n
  simp_rw [hterm'] at hswap'
  have hbase :
      (∫ y in (0 : ℝ)..1, 6 * y * (1-y)^2 / (1-y^6)) =
        Real.log (27 / 16) := by
    calc
      (∫ y in (0 : ℝ)..1, 6 * y * (1-y)^2 / (1-y^6)) =
          ∑' n : ℕ, 1 / (((2*(n:ℝ)+1) * (3*(n:ℝ)+1) * (3*(n:ℝ)+2))) :=
        hswap'.symm
      _ = Real.log (27 / 16) :=
        ErlerGross.B3_cubic_reciprocal_series_closed_form.tsum_eq
  calc
    6 * (∫ y in (0 : ℝ)..1, y * (1-y)^2 / (1-y^6)) =
        ∫ y in (0 : ℝ)..1, 6 * (y * (1-y)^2 / (1-y^6)) :=
      (intervalIntegral.integral_const_mul 6
        (fun y : ℝ => y * (1-y)^2 / (1-y^6))).symm
    _ = ∫ y in (0 : ℝ)..1, 6 * y * (1-y)^2 / (1-y^6) := by
      apply intervalIntegral.integral_congr
      intro y hy
      ring
    _ = Real.log (27 / 16) := hbase

end ErlerGrossScratch

open Real Filter Topology MeasureTheory
open Set

namespace ErlerGrossScratch

noncomputable def baseR (y : ℝ) : ℝ :=
  3 * y * (1-y) / (1 + y + y^2 + y^3 + y^4 + y^5)

lemma baseR_continuousOn : ContinuousOn baseR (Set.Icc (0 : ℝ) 1) := by
  unfold baseR
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro y hy
    have hy0 : 0 ≤ y := hy.1
    positivity

lemma baseR_eq (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    baseR y = 3 * y * (1-y)^2 / (1-y^6) := by
  by_cases hyeq : y = 1
  · simp [baseR, hyeq]
  · have hden : 1 + y + y^2 + y^3 + y^4 + y^5 ≠ 0 := by
      have hy0 : 0 ≤ y := hy.1
      have : 0 < 1 + y + y^2 + y^3 + y^4 + y^5 := by positivity
      positivity
    unfold baseR
    have hfac : 1 - y^6 = (1-y) * (1 + y + y^2 + y^3 + y^4 + y^5) := by
      ring
    rw [hfac]
    have hne : 1 - y ≠ 0 := by
      intro h
      exact hyeq (sub_eq_zero.mp h).symm
    field_simp [hden, hne]

lemma baseR_integrableOn : IntegrableOn baseR (Set.Ioo (0 : ℝ) 1) := by
  exact (baseR_continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self

lemma tanh_deriv (u : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh u ^ 2) u := by
  have h := (Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u)
    (ne_of_gt (Real.cosh_pos u))
  have hfun : Real.tanh = (fun x : ℝ => Real.sinh x / Real.cosh x) := by
    funext x
    exact Real.tanh_eq_sinh_div_cosh x
  have hder :
      (Real.cosh u * Real.cosh u - Real.sinh u * Real.sinh u) /
          Real.cosh u ^ 2 = 1 / Real.cosh u ^ 2 := by
    field_simp [ne_of_gt (Real.cosh_pos u)]
    rw [Real.cosh_sq_sub_sinh_sq]
  rw [hder] at h
  rw [hfun]
  exact h

lemma tanh_image_pos : Real.tanh '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    constructor
    · rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr hu) (Real.cosh_pos u)
    · exact Real.tanh_lt_one u
  · intro hy
    refine ⟨Real.artanh y, Real.artanh_pos hy, ?_⟩
    exact Real.tanh_artanh ⟨by linarith [hy.1], hy.2⟩

lemma exp_neg_image : (fun u : ℝ => Real.exp (-(2 / 3 : ℝ) * u)) ''
    Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    constructor
    · positivity
    · rw [Real.exp_lt_one_iff]
      have hpos : 0 < (2 / 3 : ℝ) * u := mul_pos (by norm_num) hu
      linarith
  · intro hy
    let u : ℝ := -(3 / 2 : ℝ) * Real.log y
    have hu : 0 < u := by
      dsimp [u]
      have hlog : Real.log y < 0 := Real.log_neg hy.1 hy.2
      nlinarith
    refine ⟨u, hu, ?_⟩
    dsimp [u]
    rw [show -(2 / 3 : ℝ) * (-(3 / 2 : ℝ) * Real.log y) = Real.log y by ring]
    exact Real.exp_log hy.1

lemma exp_neg_deriv (u : ℝ) :
    HasDerivWithinAt (fun u : ℝ => Real.exp (-(2 / 3 : ℝ) * u))
      ((-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u)) (Set.Ioi (0 : ℝ)) u := by
  have hlin : HasDerivAt (fun u : ℝ => -(2 / 3 : ℝ) * u) (-(2 / 3 : ℝ)) u := by
    simpa using (hasDerivAt_id u).const_mul (-(2 / 3 : ℝ))
  have hw : HasDerivWithinAt (Real.exp ∘ (fun u : ℝ => -(2 / 3 : ℝ) * u))
      (Real.exp (-(2 / 3 : ℝ) * u) * (-(2 / 3 : ℝ))) (Set.Ioi (0 : ℝ)) u :=
    (Real.hasDerivAt_exp _ |>.comp u hlin).hasDerivWithinAt
  simpa only [Function.comp_def, mul_comm] using hw

lemma exp_neg_antitone : AntitoneOn (fun u : ℝ => Real.exp (-(2 / 3 : ℝ) * u))
    (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  rw [Real.exp_le_exp]
  nlinarith

end ErlerGrossScratch
open Real Filter Topology MeasureTheory Set
namespace ErlerGrossScratch

noncomputable def H (t : ℝ) : ℝ := Real.cosh ((2 / 3 : ℝ) * Real.artanh t)
noncomputable def hg (t : ℝ) : ℝ := (H t - 1) / t

lemma exp_neg_basic {u : ℝ} (hu : 0 < u) :
    0 < Real.exp (-(2 / 3 : ℝ) * u) ∧ Real.exp (-(2 / 3 : ℝ) * u) < 1 := by
  constructor
  · positivity
  · rw [Real.exp_lt_one_iff]
    have hpos : 0 < (2 / 3 : ℝ) * u := mul_pos (by norm_num) hu
    linarith

lemma tanh_weight (u : ℝ) (hu : 0 < u) :
    |1 / Real.cosh u ^ 2| * hg (Real.tanh u) =
      2 * (Real.exp (-(2 / 3 : ℝ) * u))^2 *
        (1 - Real.exp (-(2 / 3 : ℝ) * u))^2 /
        (1 - (Real.exp (-(2 / 3 : ℝ) * u))^6) := by
  let y : ℝ := Real.exp (-(2 / 3 : ℝ) * u)
  have hy := exp_neg_basic hu
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have ht : 0 < Real.tanh u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have hyne : y ≠ 0 := ne_of_gt hy.1
  have hyeq : y ^ 6 ≠ 1 := by
    have : y ^ 6 < (1 : ℝ) := pow_lt_one₀ hy.1.le hy.2 (by norm_num)
    linarith
  have hsne : Real.sinh u ≠ 0 := ne_of_gt hs
  have hcne : Real.cosh u ≠ 0 := ne_of_gt hc
  have htne : Real.tanh u ≠ 0 := ne_of_gt ht
  have hden : 1 - y ^ 6 ≠ 0 := sub_ne_zero.mpr hyeq.symm
  have hsimp :
      |1 / Real.cosh u ^ 2| *
          ((Real.cosh ((2 / 3 : ℝ) * u) - 1) /
            (Real.sinh u / Real.cosh u)) =
        2 * (Real.cosh ((2 / 3 : ℝ) * u) - 1) / Real.sinh (2 * u) := by
    rw [abs_of_pos (by positivity : 0 < 1 / Real.cosh u ^ 2), Real.sinh_two_mul]
    field_simp [hcne, hsne]
  unfold hg H
  rw [Real.artanh_tanh, Real.tanh_eq_sinh_div_cosh]
  rw [hsimp]
  have hearg : Real.exp ((2 / 3 : ℝ) * u) = y⁻¹ := by
    dsimp [y]
    rw [← Real.exp_neg]
    congr 1
    ring
  have heargneg : Real.exp (-((2 / 3 : ℝ) * u)) = y := by
    dsimp [y]
    congr 1
    ring
  have hneg_2u : Real.exp (-(2 * u)) = y^3 := by
    have h3 := Real.exp_nat_mul (-(2 / 3 : ℝ) * u) 3
    have h3' : Real.exp (3 * (-(2 / 3 : ℝ) * u)) =
        Real.exp (-(2 / 3 : ℝ) * u)^3 := by
      simpa only [Nat.cast_ofNat] using h3
    rw [show (3 : ℝ) * (-(2 / 3 : ℝ) * u) = -(2 * u) by ring] at h3'
    simpa [y] using h3'
  have hpos_2u : Real.exp (2 * u) = (y^3)⁻¹ := by
    have h := congrArg (fun z : ℝ => z⁻¹) (Real.exp_neg (2 * u))
    calc
      Real.exp (2 * u) = (Real.exp (-(2 * u)))⁻¹ := by simpa using h.symm
      _ = (y^3)⁻¹ := by rw [hneg_2u]
  simp only [Real.cosh_eq, Real.sinh_eq]
  rw [hearg, heargneg, hpos_2u, hneg_2u]
  change 2 * ((y⁻¹ + y) / 2 - 1) /
      (((y^3)⁻¹ - y^3) / 2) =
    2 * y^2 * (1-y)^2 / (1-y^6)
  field_simp [hyne, hden]
  ring

lemma exp_weight (u : ℝ) (hu : 0 < u) :
    -((-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u)) *
        (3 * Real.exp (-(2 / 3 : ℝ) * u) *
          (1 - Real.exp (-(2 / 3 : ℝ) * u))^2 /
          (1 - (Real.exp (-(2 / 3 : ℝ) * u))^6)) =
      2 * (Real.exp (-(2 / 3 : ℝ) * u))^2 *
        (1 - Real.exp (-(2 / 3 : ℝ) * u))^2 /
        (1 - (Real.exp (-(2 / 3 : ℝ) * u))^6) := by
  have hy := exp_neg_basic hu
  have hden : 1 - (Real.exp (-(2 / 3 : ℝ) * u))^6 ≠ 0 := by
    have hlt : (Real.exp (-(2 / 3 : ℝ) * u))^6 < (1 : ℝ) :=
      pow_lt_one₀ hy.1.le hy.2 (by norm_num)
    linarith
  field_simp [hden]

end ErlerGrossScratch
namespace ErlerGrossScratch

lemma hq_integrable :
    IntegrableOn (fun y : ℝ =>
      3 * y * (1-y)^2 / (1-y^6)) (Set.Ioo (0 : ℝ) 1) := by
  apply baseR_integrableOn.congr_fun
  · intro y hy
    exact baseR_eq y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  · exact measurableSet_Ioo

lemma tanh_integrable_iff (g : ℝ → ℝ) :
    IntegrableOn g (Set.Ioo (0 : ℝ) 1) ↔
      IntegrableOn (fun u : ℝ =>
        |1 / Real.cosh u ^ 2| • g (Real.tanh u)) (Set.Ioi (0 : ℝ)) := by
  rw [← tanh_image_pos]
  exact integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun u hu => (tanh_deriv u).hasDerivWithinAt)
    Real.tanh_injective.injOn g

lemma exp_integrable_iff (q : ℝ → ℝ) :
    IntegrableOn q (Set.Ioo (0 : ℝ) 1) ↔
      IntegrableOn (fun u : ℝ =>
        -((-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u)) •
          q (Real.exp (-(2 / 3 : ℝ) * u))) (Set.Ioi (0 : ℝ)) := by
  rw [← exp_neg_image]
  exact integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn
    (s := Set.Ioi (0 : ℝ))
    (f := fun u : ℝ => Real.exp (-(2 / 3 : ℝ) * u))
    (f' := fun u : ℝ => (-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u))
    (g := q)
    measurableSet_Ioi (fun u hu => exp_neg_deriv u) exp_neg_antitone

lemma scalar_H_integral :
    IntegrableOn (fun t : ℝ =>
      (Real.cosh ((2 / 3 : ℝ) * Real.artanh t) - 1) / t)
      (Set.Ioo (0 : ℝ) 1) ∧
      2 * (∫ t in (0 : ℝ)..1,
        (Real.cosh ((2 / 3 : ℝ) * Real.artanh t) - 1) / t) =
        Real.log (27 / 16) := by
  let g : ℝ → ℝ := fun t =>
    (Real.cosh ((2 / 3 : ℝ) * Real.artanh t) - 1) / t
  let q : ℝ → ℝ := fun y =>
    3 * y * (1-y)^2 / (1-y^6)
  have hqint : IntegrableOn q (Set.Ioo (0 : ℝ) 1) := by
    simpa [q] using hq_integrable
  have hqexp := (exp_integrable_iff q).mp hqint
  have hpoint : Set.EqOn
      (fun u : ℝ =>
        -((-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u)) •
          q (Real.exp (-(2 / 3 : ℝ) * u)))
      (fun u : ℝ => |1 / Real.cosh u ^ 2| • g (Real.tanh u))
      (Set.Ioi (0 : ℝ)) := by
    intro u hu
    have ht := tanh_weight u hu
    have he := exp_weight u hu
    dsimp [g, q]
    calc
      -((-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u)) •
          (3 * Real.exp (-(2 / 3 : ℝ) * u) *
            (1 - Real.exp (-(2 / 3 : ℝ) * u))^2 /
            (1 - (Real.exp (-(2 / 3 : ℝ) * u))^6)) =
          2 * (Real.exp (-(2 / 3 : ℝ) * u))^2 *
            (1 - Real.exp (-(2 / 3 : ℝ) * u))^2 /
            (1 - (Real.exp (-(2 / 3 : ℝ) * u))^6) := by
        simpa [smul_eq_mul] using he
      _ = |1 / Real.cosh u ^ 2| *
          ((Real.cosh ((2 / 3 : ℝ) * Real.artanh (Real.tanh u)) - 1) /
            Real.tanh u) := by
        simpa [g, hg, H, smul_eq_mul] using ht.symm
  have htrans_eq : IntegrableOn (fun u : ℝ =>
      |1 / Real.cosh u ^ 2| • g (Real.tanh u)) (Set.Ioi (0 : ℝ)) := by
    exact hqexp.congr_fun hpoint measurableSet_Ioi
  have hgint : IntegrableOn g (Set.Ioo (0 : ℝ) 1) :=
    (tanh_integrable_iff g).mpr htrans_eq
  have htan_change :
      (∫ t in Set.Ioo (0 : ℝ) 1, g t) =
        ∫ u in Set.Ioi (0 : ℝ), |1 / Real.cosh u ^ 2| • g (Real.tanh u) := by
    rw [← tanh_image_pos]
    exact integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioi
      (fun u hu => (tanh_deriv u).hasDerivWithinAt)
      Real.tanh_injective.injOn g
  have hexp_change :
      (∫ y in Set.Ioo (0 : ℝ) 1, q y) =
        ∫ u in Set.Ioi (0 : ℝ),
          -((-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u)) •
            q (Real.exp (-(2 / 3 : ℝ) * u)) := by
    rw [← exp_neg_image]
    exact integral_image_eq_integral_deriv_smul_of_antitoneOn
      (s := Set.Ioi (0 : ℝ))
      (f := fun u : ℝ => Real.exp (-(2 / 3 : ℝ) * u))
      (f' := fun u : ℝ => (-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u))
      (g := q)
      measurableSet_Ioi (fun u hu => exp_neg_deriv u) exp_neg_antitone
  have h_gq :
      (∫ t in Set.Ioo (0 : ℝ) 1, g t) =
        ∫ y in Set.Ioo (0 : ℝ) 1, q y := by
    calc
      (∫ t in Set.Ioo (0 : ℝ) 1, g t) =
          ∫ u in Set.Ioi (0 : ℝ), |1 / Real.cosh u ^ 2| • g (Real.tanh u) :=
        htan_change
      _ = ∫ u in Set.Ioi (0 : ℝ),
          -((-(2 / 3 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u)) •
            q (Real.exp (-(2 / 3 : ℝ) * u)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        exact (hpoint hu).symm
      _ = ∫ y in Set.Ioo (0 : ℝ) 1, q y := hexp_change.symm
  have hg_set_interval :
      (∫ t in (0 : ℝ)..1, g t) =
        ∫ t in Set.Ioo (0 : ℝ) 1, g t := by
    calc
      (∫ t in (0 : ℝ)..1, g t) =
          ∫ t in Set.Ioc (0 : ℝ) 1, g t :=
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)
      _ = ∫ t in Set.Ioo (0 : ℝ) 1, g t :=
        integral_Ioc_eq_integral_Ioo
  have hq_set_interval :
      (∫ y in Set.Ioo (0 : ℝ) 1, q y) =
        ∫ y in (0 : ℝ)..1, q y := by
    calc
      (∫ y in Set.Ioo (0 : ℝ) 1, q y) =
          ∫ y in Set.Ioc (0 : ℝ) 1, q y :=
        (integral_Ioc_eq_integral_Ioo).symm
      _ = ∫ y in (0 : ℝ)..1, q y :=
        (intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)).symm
  have hq_interval_base :
      (∫ y in (0 : ℝ)..1, q y) =
        3 * (∫ y in (0 : ℝ)..1, y * (1-y)^2 / (1-y^6)) := by
    have heq : (fun y : ℝ => q y) =
        (fun y : ℝ => 3 * (y * (1-y)^2 / (1-y^6))) := by
      funext y
      dsimp [q]
      ring
    rw [heq, intervalIntegral.integral_const_mul]
  constructor
  · simpa [g] using hgint
  · change 2 * (∫ t in (0 : ℝ)..1, g t) = Real.log (27 / 16)
    calc
      2 * (∫ t in (0 : ℝ)..1, g t) =
          2 * (∫ t in Set.Ioo (0 : ℝ) 1, g t) := by rw [hg_set_interval]
      _ = 2 * (∫ y in Set.Ioo (0 : ℝ) 1, q y) := by rw [h_gq]
      _ = 2 * (∫ y in (0 : ℝ)..1, q y) := by rw [hq_set_interval]
      _ = 2 * (3 * (∫ y in (0 : ℝ)..1, y * (1-y)^2 / (1-y^6))) := by
        rw [hq_interval_base]
      _ = 6 * (∫ y in (0 : ℝ)..1, y * (1-y)^2 / (1-y^6)) := by ring
      _ = Real.log (27 / 16) := scalar_rational_integral_eval

end ErlerGrossScratch

namespace ErlerGrossScratch

lemma scalar_H_integrable_exact :
    IntegrableOn (fun x : ℝ =>
      (Real.cosh ((2 / 3 : ℝ) * Real.artanh x) - 1) / x)
      (Set.Ioo (0 : ℝ) 1) := by
  exact scalar_H_integral.1

lemma scalar_H_h_eval :
    -2 * (∫ x in (0 : ℝ)..1,
      (Real.cosh ((2 / 3 : ℝ) * Real.artanh x) - 1) / x) =
      2 * ∑' n : ℕ, ErlerGross.b3Term (n + 1) := by
  have hs := scalar_H_integral.2
  have hb := ErlerGross.B3_series_closed_form.tsum_eq
  calc
    -2 * (∫ x in (0 : ℝ)..1,
        (Real.cosh ((2 / 3 : ℝ) * Real.artanh x) - 1) / x) =
        -Real.log (27 / 16) := by linarith
    _ = 2 * ∑' n : ℕ, ErlerGross.b3Term (n + 1) := by
      rw [hb]
      ring

lemma scalar_H_h_eval_log :
    -2 * (∫ x in (0 : ℝ)..1,
      (Real.cosh ((2 / 3 : ℝ) * Real.artanh x) - 1) / x) =
      -Real.log (27 / 16) := by
  linarith [scalar_H_integral.2]

end ErlerGrossScratch
/- END INLINE eg_scalar_h_eval.lean -/


lemma egB_eq_official_coeff (n : ℕ) :
    egB n = (-1 : ℝ)^n * ErlerGross.neumannA (2*n) := by
  change (-1 : ℝ)^n *
    (iteratedDeriv (2*n) (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 /
      ((2*n).factorial : ℝ)) = _
  simp [ErlerGross.neumannA]

theorem solution :
    HasSum (fun n : ℕ =>
      3 * ErlerGross.neumannMEven (n + 1) * ErlerGross.betaVec (2 * (n + 1)))
      (2 * ∑' n : ℕ, ErlerGross.b3Term (n + 1)) := by
  have hb0 : egB 0 = 1 := by
    simp [egB, egf]
  have hsecond : iteratedDeriv 2 egf 0 = -(4 / 9 : ℝ) := by
    have hiter : iteratedDeriv 2 egf 0 = deriv (deriv egf) 0 := by
      simp [iteratedDeriv_succ']
    rw [hiter, egf_second]
    norm_num [egf]
  have hb1 : egB 1 = 2 / 9 := by
    simp [egB, hsecond]
    norm_num
  have hrec : ∀ n : ℕ, 1 ≤ n →
      ((n + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) * egB (n + 1) -
        (4 * (n : ℝ)^2 + 2 / 9) * egB n +
        ((n : ℝ)-1) * (2 * (n : ℝ)-1) * egB (n-1) = 0 := by
    intro n hn
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    have hplus : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hplus, ← hcast]
    exact mode_recurrence n hn
  have hbB : ∀ n : ℕ, 0 ≤ egB n := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      rw [hb0]
      norm_num
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact (ratio_bounds_of_recurrence egB hb0 hb1 hrec n hn).1
  have hb : ∀ n : ℕ, 0 ≤ (-1 : ℝ)^n * ErlerGross.neumannA (2*n) := by
    intro n
    rw [← egB_eq_official_coeff n]
    exact hbB n
  let H : ℝ → ℝ := fun x => Real.cosh ((2 / 3 : ℝ) * Real.artanh x)
  have htail (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
      HasSum
        (fun n : ℕ =>
          ((-1 : ℝ)^(n+1) * ErlerGross.neumannA (2*(n+1))) * x^(2*(n+1)))
        (Real.cosh ((2 / 3 : ℝ) * Real.artanh x) - 1) := by
    have hdiv := eg_divided_cosh_hasSum hx0 hx1
    have hmul := hdiv.mul_left x
    have hright : x * ((Real.cosh ((2 / 3 : ℝ) * Real.artanh x) - 1) / x) =
        Real.cosh ((2 / 3 : ℝ) * Real.artanh x) - 1 := by
      field_simp
    rw [hright] at hmul
    have hterm (n : ℕ) :
        x * (ErlerGross.neumannA (2*(n+1)) * (-1 : ℝ)^(n+1) * x^(2*n+1)) =
          ((-1 : ℝ)^(n+1) * ErlerGross.neumannA (2*(n+1))) * x^(2*(n+1)) := by
      ring
    exact hmul.congr_fun (fun n => (hterm n).symm)
  have hseries : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      H x - 1 = ∑' n : ℕ,
        ((-1 : ℝ)^(n+1) * ErlerGross.neumannA (2*(n+1))) * x^(2*(n+1)) := by
    intro x hx
    have ht := htail x hx.1 hx.2
    simpa [H] using ht.tsum_eq.symm
  have hseries_summable : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun n : ℕ =>
        ((-1 : ℝ)^(n+1) * ErlerGross.neumannA (2*(n+1))) * x^(2*(n+1))) := by
    intro x hx
    exact (htail x hx.1 hx.2).summable
  have hI := ErlerGrossScratch.scalar_H_integrable_exact
  have hEval := ErlerGrossScratch.scalar_H_h_eval
  have hInt : IntegrableOn (fun x : ℝ => (H x - 1)/x) (Set.Ioo (0 : ℝ) 1) := by
    simpa [H] using hI
  have hEval' : -2 * ∫ x in (0 : ℝ)..1, (H x - 1)/x =
      2 * ∑' n : ℕ, ErlerGross.b3Term (n+1) := by
    simpa [H] using hEval
  exact ErlerGross.mode_sum_eq_B3_of_H_expansion H hseries hseries_summable hb hInt hEval'
