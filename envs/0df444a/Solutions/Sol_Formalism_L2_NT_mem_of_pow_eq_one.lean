-- Prove2me | solution 1 for Formalism.L2.NT.mem_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:16.582866+00:00
-- url     : https://prove2.me/submissions/82408b59-41af-48e3-a2cc-1a8f8f843191

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {Ω : Type} [Field Ω]
namespace Formalism.L2.NT
theorem _root_.solution (B : ValuationSubring Ω) {z : Ω} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) : z ∈ B := by
  rcases B.mem_or_inv_mem z with hz | hz
  · exact hz
  · have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at h
      exact zero_ne_one h
    have e : z = z⁻¹ ^ (n - 1) := by
      have h1 : z ^ (n - 1) * z = 1 := by rw [← pow_succ, Nat.sub_add_cancel hn, h]
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
    rw [e]
    exact pow_mem hz _
end Formalism.L2.NT
