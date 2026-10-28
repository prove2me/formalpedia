-- Prove2me | solution 1 for BoseGIE.reducedPurity_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:03:01.257313+00:00
-- url     : https://prove2.me/submissions/21db9a3e-2a36-41ff-8be6-e8ddd84981c9

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BoseGIE_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace QB_e822

open BoseGIE

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

end QB_e822

open QB_e822 in
theorem solution :
    (∀ α β α' β' : ℝ, 0 ≤ α + β → α + β < α' + β' → α' + β' ≤ Real.pi →
        BoseGIE.reducedPurity (BoseGIE.psiEnd α' β') < BoseGIE.reducedPurity (BoseGIE.psiEnd α β)) ∧
    (∀ α β : ℝ, α + β = Real.pi → BoseGIE.ptrace₂ (BoseGIE.pureDM (BoseGIE.psiEnd α β)) = (1 / 2 : ℂ) • 1) := by
  refine ⟨fun α β α' β' h0 hlt hle => ?_, fun α β h => ptrace_pi α β h⟩
  rw [purity_eq, purity_eq]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi h0 hle hlt
  linarith
