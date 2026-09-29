-- Prove2me | solution 1 for BanditAlgorithm.gaussian_relative_entropy_formula
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-19T01:35:30.271992+00:00
-- url     : https://prove2.me/submissions/1ce752fa-2d67-4191-9052-1cd80d4cf9f2

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory InformationTheory NNReal

/-!
Source: Lattimore--Szepesvari, *Bandit Algorithms* (CUP 2020), Section 14.2,
printed p. 189 (PDF p. 198), immediately after Eq. (14.6). For Gaussian
probability measures with means `mu1`, `mu2` and common positive variance `v`,
the log-density ratio is affine in the sample. Integrating it under the first
Gaussian leaves `(mu1 - mu2)^2 / (2 * v)`.
-/

theorem solution (mu1 mu2 : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal mu1 v) (gaussianReal mu2 v) =
      ENNReal.ofReal ((mu1 - mu2) ^ 2 / (2 * (v : ℝ))) := by
  let P := gaussianReal mu1 v
  let Q := gaussianReal mu2 v
  have hPvol : P ≪ volume := gaussianReal_absolutelyContinuous mu1 hv
  have hvolQ : volume ≪ Q := gaussianReal_absolutelyContinuous' mu2 hv
  have hPQ : P ≪ Q := hPvol.trans hvolQ
  have hQvol : Q ≪ volume := gaussianReal_absolutelyContinuous mu2 hv
  have hratio :
      P.rnDeriv Q =ᵐ[Q] fun x => gaussianPDF mu1 v x / gaussianPDF mu2 v x := by
    filter_upwards [Measure.rnDeriv_eq_div hPvol hQvol,
      hQvol (rnDeriv_gaussianReal mu1 v), hQvol (rnDeriv_gaussianReal mu2 v)]
      with x hx h1 h2
    rw [hx, h1, h2]
  have hratioP :
      P.rnDeriv Q =ᵐ[P] fun x => gaussianPDF mu1 v x / gaussianPDF mu2 v x :=
    hPQ hratio
  have hllr : llr P Q =ᵐ[P] fun x =>
      ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ)) := by
    filter_upwards [hratioP] with x hx
    rw [llr, hx]
    simp only [ENNReal.toReal_div, toReal_gaussianPDF]
    rw [gaussianPDFReal, gaussianPDFReal]
    have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    have hc : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := by
      positivity
    rw [mul_div_mul_left _ _ hc, Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp]
    field_simp
    ring
  have hid : Integrable (fun x : ℝ => x) P := by
    simpa [P, Function.id_def] using (memLp_id_gaussianReal (μ := mu1) (v := v) 1).integrable (by simp)
  have haff : Integrable (fun x : ℝ =>
      ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ))) P := by
    have hlin : Integrable (fun x : ℝ =>
        (2 * (mu1 - mu2) * x + (mu2 ^ 2 - mu1 ^ 2)) / (2 * (v : ℝ))) P :=
      ((hid.const_mul (2 * (mu1 - mu2))).add (integrable_const _)).div_const _
    exact hlin.congr (ae_of_all _ fun x => by ring)
  have hllr_int : Integrable (llr P Q) P := haff.congr hllr.symm
  rw [klDiv_of_ac_of_integrable hPQ hllr_int]
  congr 1
  simp only [P, Q, probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae hllr]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  calc
    (∫ x, ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ)) ∂P) =
        (2 * (mu1 - mu2) * (∫ x, x ∂P) + (mu2 ^ 2 - mu1 ^ 2)) /
          (2 * (v : ℝ)) := by
            rw [integral_div]
            congr 1
            calc
              (∫ x, (x - mu2) ^ 2 - (x - mu1) ^ 2 ∂P) =
                  ∫ x, 2 * (mu1 - mu2) * x + (mu2 ^ 2 - mu1 ^ 2) ∂P := by
                    apply integral_congr_ae
                    exact ae_of_all _ fun x => by ring
              _ = 2 * (mu1 - mu2) * (∫ x, x ∂P) + (mu2 ^ 2 - mu1 ^ 2) := by
                    rw [integral_add (hid.const_mul _) (integrable_const _),
                      integral_const_mul, integral_const]
                    simp
    _ = (mu1 - mu2) ^ 2 / (2 * (v : ℝ)) := by
          simp [P, integral_id_gaussianReal]
          ring
