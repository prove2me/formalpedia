-- Prove2me | solution 1 for CouplingConstantRG.alphaOneLoop_isMuRunning
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T16:02:55.621867+00:00
-- url     : https://prove2.me/submissions/c67ecf42-5086-4435-b31c-1dcd7e6ba5eb

import Mathlib
import Definitions.Def_CouplingConstantDefs
import Definitions.Def_CouplingConstantRGDefs

open CouplingConstant CouplingConstantRG Real Set

theorem solution (β₀ Λ : ℝ) (hβ₀ : 0 < β₀) (hΛ : 0 < Λ) :
    IsMuRunning (-2 * β₀) (alphaOneLoop β₀ Λ) (Ioi Λ) := by
  intro μ hμ
  have hμpos : 0 < μ := lt_trans hΛ hμ
  have hΛsq : 0 < Λ ^ 2 := by positivity
  have hratio : 0 < μ ^ 2 / Λ ^ 2 := by positivity
  have hlogpos : 0 < log (μ ^ 2 / Λ ^ 2) := by
    refine log_pos ?_
    rw [one_lt_div hΛsq]
    simpa [pow_two] using mul_self_lt_mul_self (le_of_lt hΛ) hμ
  have hden : β₀ * log (μ ^ 2 / Λ ^ 2) ≠ 0 := by positivity
  have hpow : HasDerivAt (fun Q : ℝ => Q ^ 2 / Λ ^ 2) (2 * μ / Λ ^ 2) μ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_pow 2 μ).mul_const (Λ ^ 2)⁻¹
  have hlog : HasDerivAt (fun Q : ℝ => log (Q ^ 2 / Λ ^ 2)) (2 / μ) μ := by
    have hcomp := (hasDerivAt_log hratio.ne').comp μ hpow
    have hfun : (fun Q => log (Q ^ 2 / Λ ^ 2)) = log ∘ fun Q => Q ^ 2 / Λ ^ 2 := by
      funext Q; rfl
    have heq : (μ ^ 2 / Λ ^ 2)⁻¹ * (2 * μ / Λ ^ 2) = 2 / μ := by
      field_simp [hμpos.ne', hΛ.ne']
    rw [hfun, ← heq]
    exact hcomp
  have hg : HasDerivAt (fun Q : ℝ => β₀ * log (Q ^ 2 / Λ ^ 2)) (β₀ * (2 / μ)) μ :=
    hlog.const_mul β₀
  have hinv :
      HasDerivAt (fun Q : ℝ => (β₀ * log (Q ^ 2 / Λ ^ 2))⁻¹)
        (-(β₀ * (2 / μ)) / (β₀ * log (μ ^ 2 / Λ ^ 2)) ^ 2) μ :=
    hg.inv hden
  have hEq : alphaOneLoop β₀ Λ = fun Q => (β₀ * log (Q ^ 2 / Λ ^ 2))⁻¹ := by
    funext Q
    unfold alphaOneLoop
    exact one_div _
  rw [hEq]
  convert hinv using 1
  field_simp [hμpos.ne', hβ₀.ne', hlogpos.ne']
