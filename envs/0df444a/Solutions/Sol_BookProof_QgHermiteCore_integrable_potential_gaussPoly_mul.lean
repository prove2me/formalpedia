-- Prove2me | solution 1 for BookProof.QgHermiteCore.integrable_potential_gaussPoly_mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:23:21.682223+00:00
-- url     : https://prove2.me/submissions/c40191f9-feec-45bd-85cd-b8af16c3a4ba

import Definitions.Def_ChapterHermiteFunctions
set_option autoImplicit false

private theorem polynomial_exponential_bound (p : Polynomial ℝ) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |p.eval x| ≤ C * Real.exp (c * ‖x‖) := by
  refine ⟨∑ k ∈ p.support, |p.coeff k| * (k.factorial : ℝ), 1, zero_le_one, ?_⟩
  intro x
  simp only [one_mul, Real.norm_eq_abs]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    |∑ k ∈ p.support, p.coeff k * x ^ k| ≤ ∑ k ∈ p.support, |p.coeff k * x ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ p.support, (|p.coeff k| * (k.factorial : ℝ)) * Real.exp |x| := by
      apply Finset.sum_le_sum
      intro k hk
      have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
      rw [div_le_iff₀ hfac] at h
      rw [abs_mul, abs_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using h) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

open BookProof.HermiteCore MeasureTheory

private theorem potential_square_integrability {W : ℝ → ℝ} (hW : Continuous W)
    (hWb : ∃ C c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |W x| ≤ C * Real.exp (c * ‖x‖))
    (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => ((W x * (p.eval x * gaussH x) : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  rcases hWb with ⟨C, c, hc, hCbound⟩
  rcases polynomial_exponential_bound p with ⟨D, d, hd, hDbound⟩
  have hC : 0 ≤ C := by simpa using (abs_nonneg (W 0)).trans (hCbound 0)
  have hD : 0 ≤ D := by simpa using (abs_nonneg (p.eval 0)).trans (hDbound 0)
  have hdom := (memLp_two_exp_abs_mul_gaussH (c + d)).const_mul ((C * D : ℝ) : ℂ)
  apply hdom.mono
  · apply Continuous.aestronglyMeasurable
    exact Complex.continuous_ofReal.comp (hW.mul (p.continuous.mul continuous_gaussH))
  · filter_upwards with x
    have hprod : |W x| * |p.eval x| ≤ (C * D) * Real.exp ((c + d) * |x|) := by
      calc
        _ ≤ (C * Real.exp (c * ‖x‖)) * (D * Real.exp (d * ‖x‖)) :=
          mul_le_mul (hCbound x) (hDbound x) (abs_nonneg _)
            ((abs_nonneg _).trans (hCbound x))
        _ = _ := by rw [Real.norm_eq_abs, add_mul, Real.exp_add]; ring
    simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_mul,
      abs_mul, abs_of_nonneg hC, abs_of_nonneg hD,
      abs_of_pos (Real.exp_pos _), abs_of_pos (gaussH_pos x)]
    nlinarith [mul_le_mul_of_nonneg_right hprod (gaussH_pos x).le]


theorem solution {W : ℝ → ℝ} (hW : Continuous W)
    (hWb : ∃ C c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |W x| ≤ C * Real.exp (c * ‖x‖))
    (p q : Polynomial ℝ) :
    Integrable (fun x : ℝ => W x * ((p.eval x * gaussH x) * (q.eval x * gaussH x))) := by
  have h := integrable_mul_of_memLp_two (potential_square_integrability hW hWb p)
    (memLp_poly_mul_gaussH q)
  have hr : Integrable (fun x : ℝ =>
      (((W x * (p.eval x * gaussH x) : ℝ) : ℂ) *
        ((q.eval x * gaussH x : ℝ) : ℂ)).re) := h.re
  simpa only [← Complex.ofReal_mul, Complex.ofReal_re, mul_assoc] using hr
#print axioms solution
