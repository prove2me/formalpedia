-- Prove2me | solution 1 for Formalism.landauIteratedDerivatives.logpow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:28.11579+00:00
-- url     : https://prove2.me/submissions/2e92af83-520e-47e1-8519-8537371ae4d8

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open Formalism.landauIteratedDerivatives
namespace Formalism.landauIteratedDerivatives
theorem _root_.solution (n : ℕ) {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ n ≤ (((n : ℝ) + 1) / ε) ^ n * x ^ ε := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set η : ℝ := ε / ((n : ℝ) + 1) with hη
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hηpos : 0 < η := div_pos hε hn1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ x ^ η / η := Real.log_le_rpow_div hx0 hηpos
  have h2 : Real.log x ^ n ≤ (x ^ η / η) ^ n := pow_le_pow_left₀ hlog0 h1 n
  have h3 : (x ^ η / η) ^ n = (1 / η) ^ n * x ^ (η * n) := by
    rw [Real.rpow_mul_natCast hx0, div_pow, one_div_pow]; ring
  have h4 : x ^ (η * n) ≤ x ^ ε := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ hn1]
    nlinarith
  have h5 : 1 / η = ((n : ℝ) + 1) / ε := by rw [hη]; field_simp
  calc Real.log x ^ n ≤ (x ^ η / η) ^ n := h2
    _ = (1 / η) ^ n * x ^ (η * n) := h3
    _ ≤ (1 / η) ^ n * x ^ ε := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (((n : ℝ) + 1) / ε) ^ n * x ^ ε := by rw [h5]
end Formalism.landauIteratedDerivatives
