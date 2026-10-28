-- Prove2me | solution 1 for BMV2017.reducedPurity_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:03:00.202363+00:00
-- url     : https://prove2.me/submissions/3d093be1-66c1-48e9-aa65-df599a4a82f7

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BMV2017_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace QB_bdca

open BMV2017

lemma expI (x : ℝ) : Complex.exp (↑x * Complex.I) = ↑(Real.cos x) + ↑(Real.sin x) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma purity_eq (α β : ℝ) : reducedPurity (psiEnd α β) = 1/2 + (1 + Real.cos (α + β)) / 4 := by
  simp only [reducedPurity, ptrace₂, pureDM, psiEnd, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.of_apply, Matrix.diag, expI]
  rw [Real.cos_add]
  have h1 := Real.sin_sq_add_cos_sq α
  have h2 := Real.sin_sq_add_cos_sq β
  generalize Real.cos α = ca at *
  generalize Real.sin α = sa at *
  generalize Real.cos β = cb at *
  generalize Real.sin β = sb at *
  simp [Complex.mul_re, Complex.mul_im]
  linear_combination ((sa^2+ca^2+5)/16) * h1 + ((sb^2+cb^2+5)/16) * h2

lemma ptrace_pi (α β : ℝ) (h : α + β = Real.pi) : ptrace₂ (pureDM (psiEnd α β)) = (1 / 2 : ℂ) • 1 := by
  have hb : β = Real.pi - α := by linarith
  subst hb
  have h1 := Real.sin_sq_add_cos_sq α
  unfold psiEnd
  simp only [expI, Real.cos_pi_sub, Real.sin_pi_sub]
  generalize Real.cos α = ca at *
  generalize Real.sin α = sa at *
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [ptrace₂, pureDM, Fin.sum_univ_two] <;> refine Complex.ext ?_ ?_ <;> simp <;> nlinarith

end QB_bdca

open QB_bdca in
theorem solution :
    (∀ α β α' β' : ℝ, 0 ≤ α + β → α + β < α' + β' → α' + β' ≤ Real.pi →
        BMV2017.reducedPurity (BMV2017.psiEnd α' β') < BMV2017.reducedPurity (BMV2017.psiEnd α β)) ∧
    (∀ α β : ℝ, α + β = Real.pi → BMV2017.ptrace₂ (BMV2017.pureDM (BMV2017.psiEnd α β)) = (1 / 2 : ℂ) • 1) := by
  refine ⟨fun α β α' β' h0 hlt hle => ?_, fun α β h => ptrace_pi α β h⟩
  rw [purity_eq, purity_eq]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi h0 hle hlt
  linarith
