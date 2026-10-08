-- Prove2me | solution 1 for BalkemaDeHaan.FiniteT.sigma_pos_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:30:02.427877+00:00
-- url     : https://prove2.me/submissions/f8d196ca-7abe-4dd0-b05d-b6e501adf1a5

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
open BalkemaDeHaan.FiniteT
open MeasureTheory Set
private theorem inner_cont (u : ℝ) :
    Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, Real.exp (-(u*s))) := by
  exact (intervalIntegral.differentiable_integral_of_continuous (by fun_prop)).continuous
private theorem inner_formula (u t : ℝ) (hu : u ≠ 0) :
    (∫ s in (0 : ℝ)..t, Real.exp (-(u*s))) = (1 - Real.exp (-(u*t))) / u := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.exp) (a := 0) (b := t) (-u)
  rw [integral_exp] at h
  simp only [mul_zero, Real.exp_zero] at h
  have he : (fun s : ℝ => Real.exp (-u * s)) = (fun s => Real.exp (-(u*s))) := by
    ext s; congr 1; ring
  rw [he] at h
  simp only [neg_mul] at h
  apply (eq_div_iff hu).mpr
  nlinarith [h]

/-- Proof of Lemma 4, p. 803: `σ(u) = u⁻²(e^{-u} - 1 + u) = ∫₀¹ ∫₀ᵗ e^{-u s} ds dt` (for `u ≠ 0`)
is positive and (strictly) decreasing in `u`. -/
theorem solution :
    (∀ u : ℝ, u ≠ 0 → sigma u = (u ^ 2)⁻¹ * (Real.exp (-u) - 1 + u)) ∧
      (∀ u : ℝ, 0 < sigma u) ∧ StrictAnti sigma := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    unfold sigma
    simp_rw [inner_formula u _ hu]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const, inner_formula u 1 hu]
      simp only [sub_zero, smul_eq_mul, mul_one]
      field_simp
      <;> ring
    · exact continuous_const.intervalIntegrable _ _
    · exact (show Continuous (fun t : ℝ => Real.exp (-(u*t))) by fun_prop).intervalIntegrable _ _
  · intro u
    unfold sigma
    apply intervalIntegral.integral_pos (by norm_num) (inner_cont u).continuousOn
    · intro t ht
      exact intervalIntegral.integral_nonneg_of_forall ht.1.le (fun s => (Real.exp_pos _).le)
    · refine ⟨1, by norm_num, ?_⟩
      exact intervalIntegral.integral_pos (by norm_num) (by fun_prop)
        (fun s _ => (Real.exp_pos _).le) ⟨0, by norm_num, Real.exp_pos _⟩
  · intro u v huv
    unfold sigma
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num) (inner_cont v).continuousOn (inner_cont u).continuousOn
    · intro t ht
      apply intervalIntegral.integral_mono_on ht.1.le
        (by exact (show Continuous (fun s : ℝ => Real.exp (-(v*s))) by fun_prop).intervalIntegrable _ _)
        (by exact (show Continuous (fun s : ℝ => Real.exp (-(u*s))) by fun_prop).intervalIntegrable _ _)
      intro s hs
      apply Real.exp_le_exp.mpr
      nlinarith [hs.1]
    · refine ⟨1, by norm_num, ?_⟩
      apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (by norm_num) (by fun_prop) (by fun_prop)
      · intro s hs
        apply Real.exp_le_exp.mpr
        nlinarith [hs.1]
      · refine ⟨1, by norm_num, ?_⟩
        apply Real.exp_lt_exp.mpr
        nlinarith


#print axioms solution
