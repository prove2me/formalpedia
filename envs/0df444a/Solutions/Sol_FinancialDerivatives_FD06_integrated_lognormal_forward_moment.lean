-- Prove2me | solution 1 for FinancialDerivatives.FD06.integrated_lognormal_forward_moment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:29:54.821671+00:00
-- url     : https://prove2.me/submissions/24f4e854-3b4c-43ea-8789-994b48c6faad

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedPut
import Definitions.Def_fd06_discountedCallGaussian
import Definitions.Def_fd06_discountedPutGaussian
import Definitions.Def_fd06_deterministicForward

open FinancialDerivatives.FD06 MeasureTheory ProbabilityTheory

lemma G_fwd_ci (y : ℝ) : (gaussianReal 0 1).real (Set.Ici y) = standardNormalCDF (-y) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := (0:ℝ)) (v := 1))
  rw [standardNormalCDF, cdf_eq_real]
  conv_rhs => rw [← hmap]
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext x; simp

lemma G_fwd_symm (x : ℝ) : standardNormalCDF (-x) = 1 - standardNormalCDF x := by
  have := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (v := 1) one_ne_zero
  rw [← G_fwd_ci, standardNormalCDF, cdf_eq_real, ← measureReal_congr (Iio_ae_eq_Iic (μ := gaussianReal 0 1)),
    ← probReal_compl_eq_one_sub measurableSet_Iio, Set.compl_Iio]

lemma G_fwd_tilt (a b : ℝ) : (∫ z : ℝ, Real.exp (a + b * z) ∂gaussianReal 0 1) = Real.exp (a + b ^ 2 / 2) := by
  simp_rw [Real.exp_add]
  rw [integral_const_mul]
  have := mgf_gaussianReal (μ := (0:ℝ)) (v := 1) (p := gaussianReal 0 1) (X := id) (by simp) b
  rw [mgf] at this
  simp only [id] at this
  rw [this]; simp

lemma G_fwd_rtail (b c : ℝ) : (∫ z : ℝ, (if c ≤ z then Real.exp (b * z) else 0) ∂gaussianReal 0 1) = Real.exp (b ^ 2 / 2) * standardNormalCDF (b - c) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : ∀ z : ℝ, gaussianPDFReal 0 1 z • (if c ≤ z then Real.exp (b * z) else 0)
      = Real.exp (b ^ 2 / 2) * (gaussianPDFReal b 1 z • (Set.Ici c).indicator 1 z) := by
    intro z
    simp only [Set.indicator, Set.mem_Ici, smul_eq_mul, Pi.one_apply]
    split_ifs
    · rw [gaussianPDFReal, gaussianPDFReal]
      simp only [NNReal.coe_one, mul_one, sub_zero]
      rw [mul_assoc, ← Real.exp_add, mul_left_comm (Real.exp _), ← Real.exp_add]
      congr 2; ring
    · simp
  simp_rw [hpt]
  rw [integral_const_mul, ← integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_indicator_one measurableSet_Ici]
  congr 1
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => x + b) = gaussianReal b 1 := by
    simpa using (gaussianReal_map_add_const (μ := (0:ℝ)) (v := 1) b)
  rw [← hmap, map_measureReal_apply (by fun_prop) measurableSet_Ici]
  have : (fun x : ℝ => x + b) ⁻¹' Set.Ici c = Set.Ici (c - b) := by
    ext x; simp
  rw [this, G_fwd_ci, neg_sub]

lemma G_fwd_iff {S K R Q V : ℝ} (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) (z : ℝ) :
    K ≤ lognormalTerminal S R Q V z ↔ -generalisedD2 S K R Q V ≤ z := by
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hd : -generalisedD2 S K R Q V * Real.sqrt V = Real.log K - Real.log S - (R - Q - V/2) := by
    unfold generalisedD2 generalisedD1
    rw [Real.log_div hS.ne' hK.ne', neg_mul, sub_mul, div_mul_cancel₀ _ hs.ne', Real.mul_self_sqrt hV.le]
    ring
  unfold lognormalTerminal
  rw [← Real.log_le_log_iff hK (by positivity), Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp]
  constructor
  · intro h; by_contra h'
    have := mul_lt_mul_of_pos_right (not_le.1 h') hs; linarith
  · intro h; have := mul_le_mul_of_nonneg_right h hs.le; linarith

lemma G_fwd_ii (b c : ℝ) : Integrable (fun z : ℝ => if c ≤ z then Real.exp (b * z) else 0) (gaussianReal 0 1) := by
  have := (integrable_exp_mul_gaussianReal (μ := (0:ℝ)) (v := 1) b).indicator (measurableSet_Ici (a := c))
  refine this.congr (ae_of_all _ ?_)
  intro z; simp [Set.indicator]

lemma G_fwd_LT (S R Q V z : ℝ) : lognormalTerminal S R Q V z = S * Real.exp (R - Q - V / 2) * Real.exp (Real.sqrt V * z) := by
  rw [lognormalTerminal, Real.exp_add, mul_assoc]

lemma G_fwd_LTi (S R Q V : ℝ) : Integrable (fun z => lognormalTerminal S R Q V z) (gaussianReal 0 1) := by
  simp_rw [G_fwd_LT]
  exact (integrable_exp_mul_gaussianReal _).const_mul _

lemma G_fwd_callI (S K R Q V : ℝ) : Integrable (fun z : ℝ => max (lognormalTerminal S R Q V z - K) 0) (gaussianReal 0 1) :=
  ((G_fwd_LTi S R Q V).sub (integrable_const K)).pos_part

lemma G_fwd_putI (S K R Q V : ℝ) : Integrable (fun z : ℝ => max (K - lognormalTerminal S R Q V z) 0) (gaussianReal 0 1) :=
  ((integrable_const K).sub (G_fwd_LTi S R Q V)).pos_part

lemma G_fwd_fwd (S R Q V : ℝ) (hV : 0 ≤ V) : (∫ z : ℝ, lognormalTerminal S R Q V z ∂gaussianReal 0 1) = deterministicForward S R Q := by
  unfold lognormalTerminal
  rw [integral_const_mul, G_fwd_tilt, deterministicForward, Real.sq_sqrt hV]
  congr 2; ring

lemma G_fwd_parity (S K R Q V : ℝ) : generalisedCall S K R Q V - generalisedPut S K R Q V = S * Real.exp (-Q) - K * Real.exp (-R) := by
  unfold generalisedCall generalisedPut
  rw [G_fwd_symm, G_fwd_symm]; ring

lemma G_fwd_digital (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : Real.exp (-R) * (∫ z : ℝ, (if K ≤ lognormalTerminal S R Q V z then (1 : ℝ) else 0) ∂ProbabilityTheory.gaussianReal 0 1) = Real.exp (-R) * standardNormalCDF (generalisedD2 S K R Q V) := by
  congr 1
  have : ∀ z, (if K ≤ lognormalTerminal S R Q V z then (1:ℝ) else 0)
      = if -generalisedD2 S K R Q V ≤ z then Real.exp (0 * z) else 0 := by
    intro z; simp [G_fwd_iff hS hK hV]
  simp_rw [this]; rw [G_fwd_rtail]; simp

lemma G_fwd_callT (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : discountedCallGaussian S K R Q V = generalisedCall S K R Q V := by
  unfold discountedCallGaussian generalisedCall
  have hpt : ∀ z, max (lognormalTerminal S R Q V z - K) 0
      = S * Real.exp (R - Q - V / 2) * (if -generalisedD2 S K R Q V ≤ z then Real.exp (Real.sqrt V * z) else 0)
        - K * (if -generalisedD2 S K R Q V ≤ z then Real.exp (0 * z) else 0) := by
    intro z
    by_cases h : -generalisedD2 S K R Q V ≤ z
    · have h2 := (G_fwd_iff hS hK hV z).2 h
      rw [if_pos h, if_pos h, max_eq_left (by linarith), G_fwd_LT]; simp
    · have h2 : ¬ K ≤ lognormalTerminal S R Q V z := fun h' => h ((G_fwd_iff hS hK hV z).1 h')
      rw [if_neg h, if_neg h, max_eq_right (by linarith)]; simp
  simp_rw [hpt]
  rw [integral_sub ((G_fwd_ii _ _).const_mul _) ((G_fwd_ii _ _).const_mul _), integral_const_mul,
    integral_const_mul, G_fwd_rtail, G_fwd_rtail, Real.sq_sqrt hV.le]
  have h1 : Real.sqrt V - -generalisedD2 S K R Q V = generalisedD1 S K R Q V := by
    unfold generalisedD2; ring
  have h0 : (0:ℝ) - -generalisedD2 S K R Q V = generalisedD2 S K R Q V := by ring
  rw [h1, h0]
  have he : Real.exp (-R) * Real.exp (R - Q - V / 2) * Real.exp (V / 2) = Real.exp (-Q) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Real.exp_zero, one_mul]
  linear_combination (S * standardNormalCDF (generalisedD1 S K R Q V)) * he

lemma G_fwd_dparity (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : discountedCallGaussian S K R Q V - discountedPutGaussian S K R Q V = S * Real.exp (-Q) - K * Real.exp (-R) := by
  unfold discountedCallGaussian discountedPutGaussian
  rw [← mul_sub, ← integral_sub (G_fwd_callI S K R Q V) (G_fwd_putI S K R Q V)]
  have : ∀ x : ℝ, max (x - K) 0 - max (K - x) 0 = x - K := by
    intro x; rcases le_total x K with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  simp_rw [this]
  rw [integral_sub (G_fwd_LTi S R Q V) (integrable_const K), G_fwd_fwd S R Q V hV.le, deterministicForward]
  simp only [integral_const, probReal_univ, one_smul]
  rw [mul_sub, ← mul_assoc, mul_comm (Real.exp (-R)) S, mul_assoc, ← Real.exp_add]
  ring_nf

lemma G_fwd_putT (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : discountedPutGaussian S K R Q V = generalisedPut S K R Q V := by
  have h1 := G_fwd_dparity S K R Q V hS hK hV
  have h2 := G_fwd_parity S K R Q V
  have h3 := G_fwd_callT S K R Q V hS hK hV
  linarith

theorem solution (S R Q V : ℝ) (hV : 0 ≤ V) : (∫ z : ℝ, lognormalTerminal S R Q V z ∂ProbabilityTheory.gaussianReal 0 1) = deterministicForward S R Q :=
  G_fwd_fwd S R Q V hV
