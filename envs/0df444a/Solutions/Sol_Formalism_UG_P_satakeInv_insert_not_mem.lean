-- Prove2me | solution 1 for Formalism.UG.P.satakeInv_insert_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:49.285145+00:00
-- url     : https://prove2.me/submissions/deb4cc2f-913f-46db-af81-52bc7d61566b

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
theorem _root_.solution {α : Type} [LinearOrder α] (s' S : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hS : S ⊆ s') :
    satakeInv (insert m s') S = satakeInv s' S + S.card := by
  have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
  have hmS : m ∉ S := fun h => hmS' (hS h)
  unfold satakeInv
  rw [card_eq_sum_ones S, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have e : (insert m s' \ S).filter (fun l => a < l)
      = insert m ((s' \ S).filter (fun l => a < l)) := by
    ext x
    by_cases hx : x = m
    · simp [hx, hmS, hm a (hS ha)]
    · simp [hx]
  rw [e, card_insert_of_notMem (by simp [hmS'])]
end Formalism.UG.P
