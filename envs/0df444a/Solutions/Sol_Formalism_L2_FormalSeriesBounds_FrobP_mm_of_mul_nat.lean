-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FrobP.mm_of_mul_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:54.666314+00:00
-- url     : https://prove2.me/submissions/f305f46f-6f7f-4b67-81a7-42ea306662b1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_ge_intCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_not_mm_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.FrobP
theorem _root_.solution {c : C} {m : ℕ} (hm : ¬ V.l ∣ m) (h : V.MM (c * m)) : V.MM c := by
  have hge := ge_intCast (V := V) (m : ℤ)
  unfold VF.Ge at hge
  rw [WithTop.coe_zero, Int.cast_natCast] at hge
  have h0 : V.v (m : C) = 0 := le_antisymm (not_lt.mp (not_mm_nat hm)) hge
  unfold VF.MM at h ⊢
  rwa [AddValuation.map_mul, h0, add_zero] at h
end Formalism.L2.FormalSeriesBounds.FrobP
