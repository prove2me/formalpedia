-- Prove2me | solution 1 for Formalism.UG.P.satakeInv_insert_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:48.042793+00:00
-- url     : https://prove2.me/submissions/93dedd64-6959-448a-9adf-ad01fbf65e2c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Finset
namespace Formalism.UG.P
theorem _root_.solution {α : Type} [LinearOrder α] (s' T : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hT : T ⊆ s') :
    satakeInv (insert m s') (insert m T) = satakeInv s' T := by
  have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
  have hmT : m ∉ T := fun h => hmS' (hT h)
  unfold satakeInv
  rw [sum_insert hmT]
  have e : insert m s' \ insert m T = s' \ T := by
    ext x
    by_cases hx : x = m
    · simp [hx, hmS']
    · simp [hx]
  rw [e]
  have h0 : ((s' \ T).filter (fun l => m < l)).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x hx
    exact not_lt.2 (le_of_lt (hm x (mem_sdiff.1 hx).1))
  rw [h0, zero_add]
end Formalism.UG.P
