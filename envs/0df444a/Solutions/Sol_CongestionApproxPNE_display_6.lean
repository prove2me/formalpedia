-- Prove2me | solution 1 for CongestionApproxPNE.display_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:00:21.508209+00:00
-- url     : https://prove2.me/submissions/55a76e2e-f3e2-425e-a9f5-50f8b0968be7

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

open CongestionApproxPNE in
theorem solution (d : ℕ) (hd : 4 ≤ d) :
    1 ≤ (1 + wChoice d) ^ kd d + betaChoice d * wChoice d ^ d := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hw : 0 ≤ wChoice d := by
    unfold wChoice
    exact div_nonneg (Real.log_nonneg hd') (by positivity)
  have hb : 0 ≤ betaChoice d := by
    unfold betaChoice
    have h1 : 0 ≤ (d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) := by positivity
    have h2 : 0 ≤ (1 + wChoice d) ^ d := pow_nonneg (by linarith) _
    exact div_nonneg zero_le_one (mul_nonneg h1 h2)
  have h3 : 1 ≤ (1 + wChoice d) ^ kd d := one_le_pow₀ (by linarith)
  have h4 : 0 ≤ betaChoice d * wChoice d ^ d := mul_nonneg hb (pow_nonneg hw _)
  linarith
