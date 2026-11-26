-- Prove2me | solution 1 for FD1D.node_remainder_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:46.179804+00:00
-- url     : https://prove2.me/submissions/655112fb-e855-45cc-8a1f-9cf6f95f7375

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.harmonicPotential_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {a N p q h : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hNa : 0 < N + a) (hmajor : p ≤ (N + a) * h) :
    0 ≤ p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ∧
      p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ≤ p * h ^ 2 := by
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hNa1 : 0 < N + a + 1 := by linarith
  have hh : 0 ≤ h := by
    by_contra hn
    have hhneg : h < 0 := lt_of_not_ge hn
    have : (N + a) * h < 0 := mul_neg_of_pos_of_neg hNa hhneg
    linarith
  constructor
  · positivity
  · have hp_div : p / (N + a) ≤ h := by
      apply (div_le_iff₀ hNa).2
      simpa [mul_comm] using hmajor
    have hp_div' : p / (N + a + 1) ≤ h := by
      calc
        p / (N + a + 1) ≤ p / (N + a) := by
          exact div_le_div_of_nonneg_left hp hNa (by linarith)
        _ ≤ h := hp_div
    calc
      p ^ 3 * (1 - q) / ((N + a) * (N + a + 1))
          ≤ p ^ 3 / ((N + a) * (N + a + 1)) := by
            have hp3 : 0 ≤ p ^ 3 := by positivity
            have hnum : p ^ 3 * (1 - q) ≤ p ^ 3 := by
              calc
                p ^ 3 * (1 - q) ≤ p ^ 3 * 1 :=
                  mul_le_mul_of_nonneg_left (by linarith) hp3
                _ = p ^ 3 := mul_one _
            exact div_le_div_of_nonneg_right hnum (by positivity)
      _ = p * (p / (N + a)) * (p / (N + a + 1)) := by
            field_simp
            <;> ring
      _ ≤ p * h ^ 2 := by
            have hmul :
                (p / (N + a)) * (p / (N + a + 1)) ≤ h * h :=
              mul_le_mul hp_div hp_div' (by positivity) hh
            simpa [pow_two, mul_assoc] using
              mul_le_mul_of_nonneg_left hmul hp
end FD1D
