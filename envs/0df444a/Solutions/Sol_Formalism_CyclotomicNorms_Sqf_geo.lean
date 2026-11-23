-- Prove2me | solution 1 for Formalism.CyclotomicNorms.Sqf.geo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:41.512065+00:00
-- url     : https://prove2.me/submissions/8e7a6f66-ab1f-4e5a-9df9-f125ab252c68

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.Sqf
variable {K : Type} [Field K]
namespace Formalism.CyclotomicNorms.Sqf
theorem _root_.solution (q : ℕ) (hq : 2 ≤ q) (N : ℕ) :
    ∀ k, k < N → (∑ d ∈ Icc 1 k, q ^ (N - d)) + 2 * q ^ (N - 1 - k) ≤ 2 * q ^ (N - 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have e1 : N - 1 - k = (N - 1 - (k + 1)) + 1 := by omega
    have e2 : N - (k + 1) = N - 1 - k := by omega
    rw [e2]
    rw [e1] at ih' ⊢
    rw [pow_succ] at ih' ⊢
    have hm := Nat.mul_le_mul_left (q ^ (N - 1 - (k + 1))) hq
    linarith
end Formalism.CyclotomicNorms.Sqf
