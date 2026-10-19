-- Prove2me | solution 1 for CohnElkies.exp_integral_upperGammaCenteredTruncatedKernel_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/a46a7ef0-b99f-402d-955e-491a0b0923b1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exp_integral_upperGammaCenteredLaplaceRate
import Theorems.Thm_CohnElkies_integral_upperGammaCenteredTruncatedKernel_eq_shell_sum

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (n : ℕ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
      (∏ k ∈ Finset.range (n + 1),
        ((((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) /
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
              (k : ℂ))))) *
        Complex.exp
          (-Complex.I *
            (((ℓ * T / 2 *
              (∑ k ∈ Finset.range (n + 1),
                (ℓ * η / 2 + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
  classical
  rw [integral_upperGammaCenteredTruncatedKernel_eq_shell_sum
    hℓ hη T n, Complex.exp_sum]
  simp_rw [exp_integral_upperGammaCenteredLaplaceRate
    hℓ hη T]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  congr 1
  push_cast
  simp_rw [div_eq_mul_inv]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
end CohnElkies
