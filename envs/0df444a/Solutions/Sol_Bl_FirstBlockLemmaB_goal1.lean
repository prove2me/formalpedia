-- Prove2me | solution 1 for Bl.FirstBlockLemmaB.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:31.676042+00:00
-- url     : https://prove2.me/submissions/ade98501-5d72-4967-93aa-328bfa39f8b9

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_4
open Bl Bl.FirstBlockLemmaB
namespace Bl.FirstBlockLemmaB
theorem _root_.solution :
  ∀ {R : Type u_4} [inst : CommRing.{u_4} R] {P Q : Ideal.{u_4} R} [Ideal.IsPrime.{u_4} P],
  LE.le.{u_4} P Q →
    ∀ {x : R},
      Membership.mem.{u_4, u_4} Q x →
        Not (Membership.mem.{u_4, u_4} P x) →
          LE.le.{0} (HAdd.hAdd.{0, 0, 0} (ringKrullDim.{u_4} (HasQuotient.Quotient.{u_4, u_4} R Q)) 1)
            (ringKrullDim.{u_4} (HasQuotient.Quotient.{u_4, u_4} R P)) := by
  intro R _ P Q _ hPQ x hxQ hxP
  have hne : Ideal.Quotient.mk P x ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P x)
    (mem_nonZeroDivisors_of_ne_zero hne) ?_
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact hxQ
end Bl.FirstBlockLemmaB
