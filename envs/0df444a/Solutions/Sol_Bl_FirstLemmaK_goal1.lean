-- Prove2me | solution 1 for Bl.FirstLemmaK.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:55.770358+00:00
-- url     : https://prove2.me/submissions/1323bd04-7422-4ba6-b4e9-d3bd842a4b4f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstLemmaK
namespace Bl.FirstLemmaK
theorem _root_.solution :
  ∀ {α : Type} {S : Set.{0} α},
  Set.Finite.{0} S →
    ∀ (f : α → Real),
      (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} 0 (f x)) →
        Exists.{1} fun (r : Real) ↦
          And (LT.lt.{0} 0 r) (And (LE.le.{0} r 1) (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} r (f x))) := by
  intro α S hS f hf
  rcases S.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    intro x hx
    rw [h] at hx
    exact absurd hx (Set.notMem_empty x)
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S f hS hne
    have hfa : 0 < f a := hf a ha
    refine ⟨min (f a) 1 / 2, ?_, ?_, ?_⟩
    · have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith
    · have : min (f a) 1 ≤ 1 := min_le_right _ _
      linarith
    · intro x hx
      have h1 : min (f a) 1 ≤ f a := min_le_left _ _
      have h2 : f a ≤ f x := hmin x hx
      have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith
end Bl.FirstLemmaK
