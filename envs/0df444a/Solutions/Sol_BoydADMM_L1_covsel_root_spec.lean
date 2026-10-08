-- Prove2me | solution 1 for BoydADMM.L1.covsel_root_spec
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T07:40:56.991273+00:00
-- url     : https://prove2.me/submissions/e7c0b125-0f27-4518-b144-891709a83a09

import Definitions.Def_BoydADMM_L1_CovSel
set_option autoImplicit false
section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1
 theorem scalar_root (ρ μ : ℝ) (hρ : 0 < ρ) :
    0 < covselRoot ρ μ ∧ ρ * covselRoot ρ μ - 1 / covselRoot ρ μ = μ := by
  have hd : 0 ≤ μ ^ 2 + 4 * ρ := by positivity
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg (μ ^ 2 + 4 * ρ)
  have hp : 0 < μ + Real.sqrt (μ ^ 2 + 4 * ρ) := by
    nlinarith [sq_nonneg (μ + Real.sqrt (μ ^ 2 + 4 * ρ))]
  have ht : 0 < covselRoot ρ μ := div_pos hp (by positivity)
  refine ⟨ht, ?_⟩
  have he : ρ * (covselRoot ρ μ) ^ 2 - μ * covselRoot ρ μ - 1 = 0 := by
    unfold covselRoot
    field_simp
    simp only [mul_comm ρ 4] at *
    nlinarith
  apply (mul_right_cancel₀ (ne_of_gt ht))
  field_simp
  nlinarith [he]
end ADMMCodex

end

set_option autoImplicit false
open Matrix BoydADMM.L1
theorem solution (ρ μ : ℝ) (hρ : 0 < ρ) :
    0 < covselRoot ρ μ ∧ ρ * covselRoot ρ μ - 1 / covselRoot ρ μ = μ := by
  exact ADMMCodex.scalar_root ρ μ hρ



#print axioms solution
