-- Prove2me | solution 1 for EthierKurtz.gaussian_density_perturbation_tail_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:19:00.811537+00:00
-- url     : https://prove2.me/submissions/fd3747c0-fbee-4b1e-9910-8caa02a52f92

import Mathlib.Tactic
import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_density_perturbation_normalization
import Theorems.Thm_OAI_GaussianPropeller_Mills_inverse_mills_ratio_deriv_le_one

open MeasureTheory Set ProbabilityTheory

namespace LoAux

local notation "Ncdf" => ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))

noncomputable def T (r : ℝ) : ℝ := ∫ t in Set.Ioi r, Real.exp (-t^2/2)
noncomputable def g (x : ℝ) : ℝ := (√(2 * Real.pi))⁻¹ * Real.exp (-(x^2/2))

lemma integrable_E : Integrable (fun t : ℝ => Real.exp (-t^2/2)) := by
  have := integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only; congr 1; ring

lemma T_pos (r : ℝ) : 0 < T r := by
  unfold T
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => (Real.exp_pos _).le)
    integrable_E.integrableOn]
  have : Function.support (fun t : ℝ => Real.exp (-t^2/2)) = univ := by
    ext t; simp [(Real.exp_pos _).ne']
  rw [this, univ_inter, Real.volume_Ioi]; simp

lemma gauss_real_eq (S : Set ℝ) (hS : MeasurableSet S) :
    (gaussianReal 0 1).real S = ∫ t in S, gaussianPDFReal 0 1 t := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg hS fun _ _ => gaussianPDFReal_nonneg _ _ _)]

lemma psi_eq_int (r : ℝ) : 1 - Ncdf r = ∫ t in Ioi r, gaussianPDFReal 0 1 t := by
  rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, compl_Iic,
    gauss_real_eq _ measurableSet_Ioi]

lemma psi_eq (r : ℝ) : 1 - Ncdf r = (√(2 * Real.pi))⁻¹ * T r := by
  rw [psi_eq_int]
  unfold T
  rw [← integral_const_mul]
  congr 1; ext t
  simp [gaussianPDFReal]

lemma psi_nonneg (r : ℝ) : 0 ≤ 1 - Ncdf r := sub_nonneg.2 (cdf_le_one _ _)

lemma shift_Ioi (f : ℝ → ℝ) (a d : ℝ) :
    ∫ t in Ioi (a + d), f t = ∫ t in Ioi a, f (t + d) := by
  have A : MeasurableEmbedding fun x : ℝ => x + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have := MeasurableEmbedding.setIntegral_map (μ := volume) A f (Ioi (a + d))
  rw [map_add_right_eq_self] at this
  rw [this, preimage_add_const_Ioi, add_sub_cancel_right]

lemma T_shift {a d : ℝ} (_ha : 0 ≤ a) (hd : 0 ≤ d) :
    T (a + d) ≤ Real.exp (-(a * d)) * T a := by
  unfold T
  rw [shift_Ioi (fun t => Real.exp (-t^2/2)), ← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
  · exact (integrable_E.comp_add_right d).integrableOn
  · exact (integrable_E.const_mul _).integrableOn
  · intro t ht
    have ht' : a < t := ht
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg hd (sub_nonneg.2 ht'.le), mul_nonneg hd _ha]

lemma psi_shift {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    1 - Ncdf (a + d) ≤ (1 - Ncdf a) * Real.exp (-(a * d)) := by
  rw [psi_eq, psi_eq]
  have hs : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  calc (√(2 * Real.pi))⁻¹ * T (a + d) ≤ (√(2 * Real.pi))⁻¹ * (Real.exp (-(a * d)) * T a) :=
        mul_le_mul_of_nonneg_left (T_shift ha hd) hs
    _ = _ := by ring

lemma T_sub {a b : ℝ} : T a - T b = ∫ t in a..b, Real.exp (-t^2/2) := by
  unfold T
  exact intervalIntegral.integral_Ioi_sub_Ioi' integrable_E.integrableOn integrable_E.integrableOn

lemma psi_sub (a b : ℝ) : (1 - Ncdf a) - (1 - Ncdf b) = ∫ x in a..b, g x := by
  rw [psi_eq, psi_eq, ← mul_sub, T_sub, ← intervalIntegral.integral_const_mul]
  congr 1; ext x; unfold g; rw [neg_div]

lemma g_cont : Continuous g := by unfold g; fun_prop

lemma g_nonneg (x : ℝ) : 0 ≤ g x := by unfold g; positivity

lemma E_le {s : ℝ} (hs : 0 ≤ s) : Real.exp (-s^2/2) ≤ (s+1) * T s := by
  have h1 := OAI.GaussianPropeller.Mills.inverse_mills_ratio_deriv_le_one s
  have hT := T_pos s
  change Real.exp (-s^2/2) / T s * (Real.exp (-s^2/2) / T s - s) ≤ 1 at h1
  have key : Real.exp (-s^2/2) / T s ≤ s + 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [div_le_iff₀ hT] at key
  linarith

lemma g_le_psi {s : ℝ} (hs : 0 ≤ s) : g s ≤ (s+1) * (1 - Ncdf s) := by
  rw [psi_eq]; unfold g; rw [← neg_div]
  have := E_le hs
  have hc : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  calc _ ≤ (√(2 * Real.pi))⁻¹ * ((s+1) * T s) := mul_le_mul_of_nonneg_left this hc
    _ = _ := by ring

lemma cube_int {s R : ℝ} (_hsR : s ≤ R) :
    ∫ x in s..R, x^3 * Real.exp (-(x^2/2)) ≤ (s^2+2) * Real.exp (-(s^2/2)) := by
  have hd : ∀ x ∈ uIcc s R, HasDerivAt (fun x : ℝ => -(x^2+2) * Real.exp (-(x^2/2)))
      (x^3 * Real.exp (-(x^2/2))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -(x^2/2)) (-x) x := by
      have h0 : HasDerivAt (fun x : ℝ => -(x^2/2)) (-(↑(2:ℕ) * x ^ (2 - 1) / 2)) x :=
        ((hasDerivAt_pow 2 x).div_const 2).neg
      exact h0.congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun x : ℝ => -(x^2+2) * Real.exp (-(x^2/2)))
        (-(↑(2:ℕ) * x ^ (2 - 1)) * Real.exp (-(x ^ 2 / 2)) +
          (-(x^2+2)) * (Real.exp (-(x ^ 2 / 2)) * -x)) x :=
      ((hasDerivAt_pow 2 x).add_const 2).neg.mul h1.exp
    exact h2.congr_deriv (by norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => x^3 * Real.exp (-(x^2/2))).intervalIntegrable _ _)]
  have : 0 ≤ (R^2+2) * Real.exp (-(R^2/2)) := by positivity
  linarith

lemma exp_neg_le_inv (y : ℝ) (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  rw [le_div_iff₀ hy]
  have h1 := Real.add_one_le_exp y
  have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-y)
  nlinarith

lemma exp_neg_two_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1/2) : Real.exp (-(2*z)) ≤ 1 - z := by
  have ha := Real.add_one_le_exp (2*z)
  have hp := Real.exp_pos (-(2*z))
  have e : Real.exp (-(2*z)) * Real.exp (2*z) = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp (-(2*z)) * (2*z + 1) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left ha hp.le]
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_right hc.le (show 0 ≤ 2*z+1 by linarith)]

lemma exp_neg_one_le : Real.exp (-1) ≤ 1/2 := by
  have h1 := Real.add_one_le_exp 1
  have e : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-1)
  nlinarith

lemma additive {c0 ε ε0 s R : ℝ} (hc0 : 0 ≤ c0) (hε : 0 < ε) (_hcε : c0 * ε ≤ 1)
    (hε0 : 0 < ε0) (hR : R = ε0 / ε) (hs : 1 ≤ s) (hsR : 2 * s ≤ R) :
    (1 - Ncdf s) * (1 - (7*c0 + 2/ε0) * (ε*s^3)) ≤
      ∫ x in s..R, g x * Real.exp (-(c0*ε*(1+|x|^3))) := by
  have hs0 : 0 < s := by linarith
  have hsR' : s ≤ R := by linarith
  set c := (√(2 * Real.pi))⁻¹ with hc
  have hc0' : 0 ≤ c := by positivity
  have hpt : ∀ x ∈ Icc s R, (1 - c0*ε) * g x - c0*ε*c * (x^3 * Real.exp (-(x^2/2))) ≤
      g x * Real.exp (-(c0*ε*(1+|x|^3))) := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    rw [abs_of_nonneg hx0]
    have h1 := Real.add_one_le_exp (-(c0*ε*(1+x^3)))
    have hg := g_nonneg x
    have h2 : g x * (1 - c0*ε*(1+x^3)) ≤ g x * Real.exp (-(c0*ε*(1+x^3))) :=
      mul_le_mul_of_nonneg_left (by linarith) hg
    have e : g x * (1 - c0*ε*(1+x^3)) =
        (1 - c0*ε) * g x - c0*ε*c * (x^3 * Real.exp (-(x^2/2))) := by unfold g; ring
    linarith
  have hi1 : IntervalIntegrable (fun x => (1 - c0*ε) * g x) volume s R :=
    (g_cont.const_mul _).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => c0*ε*c * (x^3 * Real.exp (-(x^2/2)))) volume s R :=
    ((by fun_prop : Continuous fun x : ℝ => c0*ε*c * (x^3 * Real.exp (-(x^2/2))))).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun x => g x * Real.exp (-(c0*ε*(1+|x|^3)))) volume s R :=
    ((by unfold g; fun_prop : Continuous fun x => g x * Real.exp (-(c0*ε*(1+|x|^3))))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hsR' (hi1.sub hi2) hi3 hpt
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← psi_sub] at hmono
  set P := 1 - Ncdf s with hP
  set Q := 1 - Ncdf R with hQ
  set I := ∫ x in s..R, x^3 * Real.exp (-(x^2/2)) with hI
  set y := ε * s^3 with hy
  have hP0 : 0 ≤ P := psi_nonneg s
  have hQ0 : 0 ≤ Q := psi_nonneg R
  have hs3 : 1 ≤ s^3 := one_le_pow₀ hs
  have hεy : ε ≤ y := by rw [hy]; nlinarith
  -- cube integral bound
  have hcI : c * I ≤ 6 * s^3 * P := by
    have h1 := mul_le_mul_of_nonneg_left (cube_int hsR') hc0'
    have h2 : c * ((s^2+2) * Real.exp (-(s^2/2))) = (s^2+2) * g s := by unfold g; ring
    have h3 := mul_le_mul_of_nonneg_left (g_le_psi hs0.le) (show 0 ≤ s^2+2 by positivity)
    have h4 : (s^2+2) * ((s+1) * P) ≤ 6 * s^3 * P := by
      have : (s^2+2)*(s+1) ≤ 6 * s^3 := by nlinarith
      nlinarith
    linarith
  have hcεI : c0*ε*c * I ≤ 6 * c0 * y * P := by
    have := mul_le_mul_of_nonneg_left hcI (mul_nonneg hc0 hε.le)
    rw [hy]; nlinarith
  -- tail at R
  have hQb : Q ≤ (2/ε0) * y * P := by
    have h1 := psi_shift hs0.le (show 0 ≤ R - s by linarith)
    rw [add_sub_cancel] at h1
    have hRpos : 0 < R := by linarith
    have h2 : Real.exp (-(s * (R - s))) ≤ Real.exp (-(R/2)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 := exp_neg_le_inv (R/2) (by linarith)
    have h4 : 1 / (R/2) ≤ (2/ε0) * y := by
      rw [hR, hy]
      have e : 1 / (ε0 / ε / 2) = 2/ε0 * ε := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hεy (by positivity)
    calc Q ≤ P * Real.exp (-(s * (R - s))) := h1
      _ ≤ P * ((2/ε0) * y) := mul_le_mul_of_nonneg_left (by linarith) hP0
      _ = _ := by ring
  have hcεP : c0 * ε * P ≤ c0 * y * P := by
    have := mul_le_mul_of_nonneg_left hεy hc0
    nlinarith
  have hcεQ : 0 ≤ c0 * ε * Q := by positivity
  nlinarith

lemma multiplicative {c0 ε s R : ℝ} (hc0 : 0 ≤ c0) (hε : 0 < ε)
    (hs : 1 ≤ s) (hsR : 2 * s ≤ R) :
    (1 - Ncdf s) * Real.exp (-1) * Real.exp (-(9*c0*(ε*s^3))) ≤
      ∫ x in s..R, g x * Real.exp (-(c0*ε*(1+|x|^3))) := by
  have hs0 : 0 < s := by linarith
  set m := s + 1/s with hm
  have h1s : 1/s ≤ 1 := by rw [div_le_one hs0]; exact hs
  have h1s0 : 0 < 1/s := by positivity
  have hsm : s ≤ m := by linarith
  have hmR : m ≤ R := by linarith
  have hcont : Continuous fun x => g x * Real.exp (-(c0*ε*(1+|x|^3))) := by unfold g; fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) s m) (hcont.intervalIntegrable (μ := volume) m R)
  have hnn : 0 ≤ ∫ x in m..R, g x * Real.exp (-(c0*ε*(1+|x|^3))) :=
    intervalIntegral.integral_nonneg hmR fun x _ => mul_nonneg (g_nonneg x) (Real.exp_pos _).le
  have hpt : ∀ x ∈ Icc s m, Real.exp (-(9*c0*(ε*s^3))) * g x ≤
      g x * Real.exp (-(c0*ε*(1+|x|^3))) := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    rw [abs_of_nonneg hx0, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (g_nonneg x)
    apply Real.exp_le_exp.2
    have hx2 : x ≤ 2 * s := by linarith [hx.2]
    have hx3 : x^3 ≤ (2*s)^3 := pow_le_pow_left₀ hx0 hx2 3
    have hs3 : 1 ≤ s^3 := one_le_pow₀ hs
    have : 1 + x^3 ≤ 9 * s^3 := by nlinarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hc0 hε.le)
    nlinarith
  have hmono := intervalIntegral.integral_mono_on hsm
    ((g_cont.const_mul _).intervalIntegrable (μ := volume) _ _) (hcont.intervalIntegrable s m) hpt
  rw [intervalIntegral.integral_const_mul, ← psi_sub] at hmono
  have hsh := psi_shift (a := s) (d := 1/s) hs0.le h1s0.le
  rw [show s * (1/s) = 1 by field_simp] at hsh
  have he1 := exp_neg_one_le
  have hP0 := psi_nonneg s
  have hE := Real.exp_pos (-(9*c0*(ε*s^3)))
  have hk : (1 - Ncdf s) * Real.exp (-1) ≤ (1 - Ncdf s) - (1 - Ncdf m) := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hk hE.le
  nlinarith

lemma combined {c0 ε ε0 s R : ℝ} (hc0 : 0 ≤ c0) (hε : 0 < ε) (hcε : c0 * ε ≤ 1)
    (hε0 : 0 < ε0) (hR : R = ε0 / ε) (hs : 1 ≤ s) (hsR : 2 * s ≤ R) :
    (1 - Ncdf s) * Real.exp (-((9*c0 + 2*(7*c0 + 2/ε0)) * (ε*s^3))) ≤
      ∫ x in s..R, g x * Real.exp (-(c0*ε*(1+|x|^3))) := by
  set C6 := 7*c0 + 2/ε0 with hC6
  set y := ε * s^3 with hy
  have hy0 : 0 ≤ y := by positivity
  have hC60 : 0 ≤ C6 := by positivity
  have hP0 := psi_nonneg s
  rcases le_or_gt (C6 * y) (1/2) with hsm | hbig
  · have h := additive hc0 hε hcε hε0 hR hs hsR
    have h2 := exp_neg_two_le (mul_nonneg hC60 hy0) hsm
    have h3 : Real.exp (-((9*c0 + 2*C6) * y)) ≤ Real.exp (-(2*(C6*y))) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc0 hy0])
    calc _ ≤ (1 - Ncdf s) * (1 - C6 * y) :=
          mul_le_mul_of_nonneg_left (h3.trans h2) hP0
      _ ≤ _ := h
  · have h := multiplicative (R := R) hc0 hε hs hsR
    have e : Real.exp (-((9*c0 + 2*C6) * y)) =
        Real.exp (-(2*C6*y)) * Real.exp (-(9*c0*y)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(2*C6*y)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    rw [e]
    calc _ ≤ (1 - Ncdf s) * (Real.exp (-1) * Real.exp (-(9*c0*y))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le) hP0
      _ = _ := by ring
      _ ≤ _ := h

end LoAux


theorem solution :
    ∀ {c0 ε0 A b : ℝ},
      (0 : ℝ) ≤ c0 →
        (0 : ℝ) < ε0 →
          c0 * ε0 ≤ (1 / 16 : ℝ) →
            (0 : ℝ) ≤ A →
              (0 : ℝ) < b →
                ∃ (cL : ℝ) (ε1 : ℝ),
                  (0 : ℝ) < cL ∧
                    (0 : ℝ) < ε1 ∧
                      ∀ (h : ℝ → ℝ) (K0 ε : ℝ),
                        (0 : ℝ) < ε ∧
                            (0 : ℝ) < K0 ∧
                              (∀ (x : ℝ), (0 : ℝ) ≤ h x) ∧
                                MeasureTheory.Integrable h MeasureTheory.MeasureSpace.volume ∧
                                  ∫ (x : ℝ), h x = (1 : ℝ) ∧
                                    (∀ (x : ℝ),
                                        |x| ≤ ε0 / ε →
                                          h x ≤
                                            K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                              Real.exp (c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ∧
                                      (∀ (x : ℝ),
                                          |x| ≤ ε0 / ε →
                                            K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                Real.exp (-(c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ≤
                                              h x) ∧
                                        ∫ (x : ℝ) in (Set.Icc (-(ε0 / ε)) (ε0 / ε))ᶜ, h x ≤
                                          A * Real.exp (-(b / ε ^ (2 : ℕ))) →
                          ε ≤ ε1 →
                            ∀ (s : ℝ),
                              (1 : ℝ) ≤ s →
                                s ≤ ε0 / (2 : ℝ) / ε →
                                  ((1 : ℝ) -
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) s) *
                                      Real.exp (-(cL * ε * s ^ (3 : ℕ))) ≤
                                    ∫ (x : ℝ) in Set.Ioi s, h x := by
  intro c0 ε0 A b hc0 hε0 hcε0 hA hb
  obtain ⟨C3, ε1', hC3, hε1', _hε1'1, hε1c, hmain⟩ :=
    EthierKurtz.gaussian_density_perturbation_normalization hc0 hε0 hcε0 hA hb
  set C7 := 9*c0 + 2*(7*c0 + 2/ε0) with hC7
  have hC70 : 0 < C7 := by positivity
  refine ⟨2*C3 + C7, min ε1' (1/(2*C3)), by positivity, lt_min hε1' (by positivity), ?_⟩
  intro h K0 ε hyp hεε1 s hs1 hs2
  obtain ⟨hK1, _hK2, -⟩ := hmain h K0 ε hyp (hεε1.trans (min_le_left _ _))
  obtain ⟨hε, hK0, hh0, hint, -, -, hlow, -⟩ := hyp
  set R := ε0 / ε with hR
  have hsR : 2 * s ≤ R := by
    have : ε0 / 2 / ε = R / 2 := by rw [hR]; ring
    linarith
  have hs0 : 0 < s := by linarith
  have hsR' : s ≤ R := by linarith
  have hcε : c0 * ε ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hεε1.trans (min_le_left _ _)) hc0
    linarith
  have hJ := LoAux.combined hc0 hε hcε hε0 hR hs1 hsR
  rw [← hC7] at hJ
  set J := ∫ x in s..R, LoAux.g x * Real.exp (-(c0*ε*(1+|x|^3))) with hJdef
  set P := 1 - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) s
  set y := ε * s^3 with hy
  have hs3 : 1 ≤ s^3 := one_le_pow₀ hs1
  have hεy : ε ≤ y := by rw [hy]; nlinarith
  -- integral of h
  have hstep1 : ∫ x in s..R, h x ≤ ∫ x in Set.Ioi s, h x := by
    rw [intervalIntegral.integral_of_le hsR']
    exact MeasureTheory.setIntegral_mono_set hint.integrableOn
      (MeasureTheory.ae_of_all _ fun x => hh0 x) (MeasureTheory.ae_of_all _ Set.Ioc_subset_Ioi_self)
  have hcont : Continuous fun x => LoAux.g x * Real.exp (-(c0*ε*(1+|x|^3))) := by
    unfold LoAux.g; fun_prop
  have hstep2 : K0 * J ≤ ∫ x in s..R, h x := by
    rw [hJdef, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hsR'
      ((hcont.const_mul K0).intervalIntegrable _ _) (hint.intervalIntegrable) ?_
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have := hlow x (by rw [abs_of_nonneg hx0]; exact hx.2)
    calc K0 * (LoAux.g x * Real.exp (-(c0*ε*(1+|x|^3)))) = _ := by unfold LoAux.g; ring
      _ ≤ h x := this
  have hK : Real.exp (-(2*C3*y)) ≤ K0 := by
    have hC3ε : C3 * ε ≤ 1/2 := by
      have := mul_le_mul_of_nonneg_left (hεε1.trans (min_le_right _ _)) hC3.le
      have e : C3 * (1/(2*C3)) = 1/2 := by field_simp
      linarith
    have h1 := LoAux.exp_neg_two_le (mul_nonneg hC3.le hε.le) hC3ε
    have h2 : Real.exp (-(2*C3*y)) ≤ Real.exp (-(2*(C3*ε))) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 := (abs_le.1 hK1).1
    linarith
  have e : Real.exp (-((2*C3 + C7) * ε * s^3)) = Real.exp (-(2*C3*y)) * Real.exp (-(C7*y)) := by
    rw [← Real.exp_add]; congr 1; rw [hy]; ring
  rw [e]
  have hP0 : 0 ≤ P := LoAux.psi_nonneg s
  calc P * (Real.exp (-(2*C3*y)) * Real.exp (-(C7*y)))
      = Real.exp (-(2*C3*y)) * (P * Real.exp (-(C7*y))) := by ring
    _ ≤ K0 * J := mul_le_mul hK hJ (by positivity) hK0.le
    _ ≤ _ := hstep2.trans hstep1
