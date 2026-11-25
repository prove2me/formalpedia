-- Prove2me | solution 1 for Bl.FirstBlockLemmaL.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:44.495015+00:00
-- url     : https://prove2.me/submissions/3a788aa8-90e2-4c23-b63a-16867539f77d

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaL
namespace Bl.FirstBlockLemmaL
theorem _root_.solution :
  ∀ (ℓ : Nat) [Fact (Nat.Prime ℓ)] (s : Multiset.{0} Nat),
  (∀ (x : Nat), Membership.mem.{0, 0} s x → Ne.{1} x 0) →
    Eq.{1} (padicValNat ℓ (Multiset.prod.{0} s)) (Multiset.sum.{0} (Multiset.map.{0, 0} (padicValNat ℓ) s)) := by
  intro ℓ _ s hs
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha : a ≠ 0 := hs a (by simp)
    have ht' : ∀ x, x ∈ t → x ≠ 0 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have ht : t.prod ≠ 0 := by
      rw [Ne, Multiset.prod_eq_zero_iff]
      intro h
      exact ht' 0 h rfl
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, padicValNat.mul ha ht, ih ht']
end Bl.FirstBlockLemmaL
