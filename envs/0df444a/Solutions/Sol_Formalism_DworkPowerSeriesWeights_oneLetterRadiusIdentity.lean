-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.oneLetterRadiusIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:25.080133+00:00
-- url     : https://prove2.me/submissions/d9ba0a8b-9fbb-44c0-93a9-ca2137894220

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : OneLetterRadius := by
  unfold OneLetterRadius
  intro l hl
  have hL : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hL1 : (1 : ℝ) ≤ l := by linarith
  refine ⟨fun α β hodd => ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity), one_mul]
    rcases Nat.eq_zero_or_pos α with ha | ha
    · subst ha
      have hb : 1 ≤ β := by
        rcases hodd with ⟨k, hk⟩
        omega
      have h1 : (l : ℝ) ^ 1 ≤ (l : ℝ) ^ β := pow_le_pow_right₀ hL1 hb
      rw [pow_zero]
      rw [pow_one] at h1
      linarith
    · have h1 : (l : ℝ) ^ 1 ≤ (l : ℝ) ^ α := pow_le_pow_right₀ hL1 ha
      have h2 : (1 : ℝ) ≤ (l : ℝ) ^ β := one_le_pow₀ hL1
      rw [pow_one] at h1
      linarith
  · unfold gam rho
    have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h2 : (l : ℝ) + 1 ≠ 0 := by linarith
    rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h1]
    ring
end Formalism.DworkPowerSeriesWeights
