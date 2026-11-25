-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.g_power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:25.049696+00:00
-- url     : https://prove2.me/submissions/ae3d1e64-4318-498a-89d3-b5cf109e5d55

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : GPowers := by
  intro m i s C ka N I A TT g hm hi hs hka hg
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  have e1 : 2 * (q + 1) - 2 = 2 * q := by omega
  have e2 : 2 * (q + 1 - 1) + (u + 1) - 1 = 2 * q + u := by omega
  have e3 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  have e4 : 2 * (q + 1 - 1) = 2 * q := by omega
  simp only [xThreshold, lamThreshold, lamPrimeSq, Nat.add_sub_cancel, e1, e2, e3, e4]
  have hg0 : g ≠ 0 := hg.ne'
  have hka0 : ka ≠ 0 := hka.ne'
  have e5 : 2 * q + (u + 1) - 1 = 2 * q + u := by omega
  simp only [e5]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
  · simp only [div_pow, inv_pow, mul_pow, mul_inv, inv_inv, div_eq_mul_inv]; field_simp; try ring
end Formalism.FourierDecayAlt.P
