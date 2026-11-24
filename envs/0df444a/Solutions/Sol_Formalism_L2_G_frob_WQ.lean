-- Prove2me | solution 1 for Formalism.L2.G.frob_WQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:32.538805+00:00
-- url     : https://prove2.me/submissions/ccd137d5-aa52-4fef-b834-2d773c235760

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
omit [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution (x : WQ p n) : ∃ y : WQ p n, WittVector.frobenius x = x ^ p + (p : WQ p n) * y := by
  set d := WittVector.frobenius x - x ^ p with hd
  have hd0 : d.coeff 0 = 0 := by
    have h1 : WittVector.constantCoeff d = 0 := by
      rw [hd, map_sub, map_pow]
      show (WittVector.frobenius x).coeff 0 - (x.coeff 0) ^ p = 0
      rw [WittVector.coeff_frobenius_charP, sub_self]
    exact h1
  by_cases h0 : d = 0
  · refine ⟨0, ?_⟩
    rw [mul_zero, add_zero]
    exact sub_eq_zero.mp h0
  obtain ⟨k, y, hy0, hy⟩ := WittVector.exists_eq_pow_p_mul d h0
  cases k with
  | zero =>
    exfalso
    rw [pow_zero, one_mul] at hy
    exact hy0 (hy ▸ hd0)
  | succ k =>
    refine ⟨(p : WQ p n) ^ k * y, ?_⟩
    have : WittVector.frobenius x = x ^ p + d := by rw [hd]; ring
    rw [this, hy]
    ring
end Formalism.L2.G
