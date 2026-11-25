-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.frobeniusSubstSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:57.6052+00:00
-- url     : https://prove2.me/submissions/f3481ce3-8aba-459a-9653-0d7a70721fb3

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution (k : Type*) [Field k] (Z : Type*) : FrobSpec k Z := by
  intro N f hN
  constructor
  · intro A
    have hA : (N • A).mapRange (· / N) (Nat.zero_div N) = A := by
      ext d
      rw [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul,
        Nat.mul_div_cancel_left _ (by omega : 0 < N)]
    show frob N f (N • A) = _
    unfold frob
    rw [if_pos (fun d => by rw [Finsupp.smul_apply, smul_eq_mul]; exact Nat.dvd_mul_right _ _), hA]
  · intro B hB
    show frob N f B = 0
    unfold frob
    rw [if_neg]
    intro hdiv
    apply hB
    refine ⟨B.mapRange (· / N) (Nat.zero_div N), ?_⟩
    ext d
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, Nat.mul_div_cancel' (hdiv d)]
end Formalism.BaseCaseIdentities
