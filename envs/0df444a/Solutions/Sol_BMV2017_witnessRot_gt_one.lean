-- Prove2me | solution 1 for BMV2017.witnessRot_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:25:16.03354+00:00
-- url     : https://prove2.me/submissions/3fd0eabc-4e77-4bda-b653-9ff660bf2327

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BMV2017_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace QB_2218

open BMV2017

lemma expI (x : ℝ) : Complex.exp (↑x * Complex.I) = ↑(Real.cos x) + ↑(Real.sin x) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma rotZ (θ : ℝ) : (phaseRot θ)ᴴ * σz * phaseRot θ = σz := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [phaseRot, expI]
  generalize Real.cos θ = c at *
  generalize Real.sin θ = s at *
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σz, Matrix.mul_apply, Fin.sum_univ_two] <;>
    refine Complex.ext ?_ ?_ <;> simp <;> nlinarith

lemma trace_formula (α β θ₁ θ₂ : ℝ) :
    (pureDM (psiEnd α β) * (((phaseRot θ₁)ᴴ * σx * phaseRot θ₁) ⊗ₖ ((phaseRot θ₂)ᴴ * σz * phaseRot θ₂))).trace -
    (pureDM (psiEnd α β) * (((phaseRot θ₁)ᴴ * σy * phaseRot θ₁) ⊗ₖ ((phaseRot θ₂)ᴴ * σy * phaseRot θ₂))).trace
    = ((1/2 * (Real.cos (β + θ₁) - Real.cos (θ₁ - α) + Real.cos (θ₁ + θ₂)
        - Real.cos (α - β + θ₂ - θ₁)) : ℝ) : ℂ) := by
  rw [rotZ]
  have e : α - β + θ₂ - θ₁ = (α + θ₂) - (β + θ₁) := by ring
  rw [e, Real.cos_add, Real.cos_sub, Real.cos_add, Real.cos_sub, Real.cos_add, Real.cos_add,
    Real.sin_add, Real.sin_add]
  simp only [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diag, Matrix.mul_apply,
    pureDM, psiEnd, phaseRot, σx, σy, σz, Matrix.kronecker_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, expI]
  generalize Real.cos α = ca
  generalize Real.sin α = sa
  generalize Real.cos β = cb
  generalize Real.sin β = sb
  generalize Real.cos θ₁ = c1
  generalize Real.sin θ₁ = s1
  generalize Real.cos θ₂ = c2
  generalize Real.sin θ₂ = s2
  refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

end QB_2218

open QB_2218 in
theorem solution :
    ∃ θ₁ θ₂ : ℝ, 1 < BMV2017.witnessRot θ₁ θ₂ (BMV2017.pureDM (BMV2017.psiEnd (-1 / 5) (7 / 10))) := by
  refine ⟨Real.pi / 2 - 9 / 20, Real.pi / 2 + 9 / 20, ?_⟩
  unfold BMV2017.witnessRot
  rw [trace_formula, Complex.norm_real, Real.norm_eq_abs]
  have e1 : (7 / 10 : ℝ) + (Real.pi / 2 - 9 / 20) = 1 / 4 + Real.pi / 2 := by ring
  have e2 : (Real.pi / 2 - 9 / 20) - (-1 / 5 : ℝ) = Real.pi / 2 - 1 / 4 := by ring
  have e3 : (Real.pi / 2 - 9 / 20) + (Real.pi / 2 + 9 / 20) = Real.pi := by ring
  have e4 : (-1 / 5 : ℝ) - 7 / 10 + (Real.pi / 2 + 9 / 20) - (Real.pi / 2 - 9 / 20) = 0 := by ring
  rw [e1, e2, e3, e4, Real.cos_add_pi_div_two, Real.cos_pi_div_two_sub, Real.cos_pi, Real.cos_zero]
  have hs : 0 < Real.sin (1 / 4) := Real.sin_pos_of_pos_of_lt_pi (by norm_num)
    (by linarith [Real.pi_gt_three])
  rw [abs_of_neg (by linarith)]
  linarith
