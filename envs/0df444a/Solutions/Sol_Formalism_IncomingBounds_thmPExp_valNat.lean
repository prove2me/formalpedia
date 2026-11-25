-- Prove2me | solution 1 for Formalism.IncomingBounds.thmPExp_valNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:33:37.568167+00:00
-- url     : https://prove2.me/submissions/066680ab-0f56-443f-b358-4e2a594c6445

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp

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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : ValNat := by
  intro K _ _ v l hl hvl hvp N hN
  have := Fact.mk hl
  induction N using Nat.recOnMul with
  | zero => exact absurd rfl hN
  | one => simp
  | prime p hp =>
    by_cases hpl : p = l
    · subst hpl; rw [hvl, padicValNat_self]; simp
    · have := Fact.mk hp
      rw [hvp p hp hpl, padicValNat_primes (Ne.symm hpl)]; simp
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := fun h => hN (by simp [h])
    have hb0 : b ≠ 0 := fun h => hN (by simp [h])
    rw [Nat.cast_mul, AddValuation.map_mul, ha ha0, hb hb0, padicValNat.mul ha0 hb0]
    push_cast
    rfl
end Formalism.IncomingBounds
