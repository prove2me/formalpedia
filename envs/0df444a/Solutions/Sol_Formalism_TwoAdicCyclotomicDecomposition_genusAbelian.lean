-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.genusAbelian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:34.920831+00:00
-- url     : https://prove2.me/submissions/571f4cea-9332-4fa8-b1bf-cf98b9b481b2

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : GenusAbelian := by
  intro G _ _ A B C hsup hcard a ha b hb c hc habc
  let f : A × B × C →* G := A.subtype.coprod (B.subtype.coprod C.subtype)
  have hf : ∀ x : A × B × C, f x = (x.1 : G) * ((x.2.1 : G) * (x.2.2 : G)) := fun x => rfl
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hsup]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx; exact ⟨(⟨x, hx⟩, 1, 1), by simp [hf]⟩
    · intro x hx; exact ⟨(1, ⟨x, hx⟩, 1), by simp [hf]⟩
    · intro x hx; exact ⟨(1, 1, ⟨x, hx⟩), by simp [hf]⟩
  have hbij : Function.Bijective f := by
    apply hsurj.bijective_of_nat_card_le
    rw [Nat.card_prod, Nat.card_prod, hcard, mul_assoc]
  have h1 : f (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) = f 1 := by
    rw [hf, map_one]; simpa [mul_assoc] using habc
  have h2 := hbij.1 h1
  simp only [Prod.mk_eq_one, Subgroup.mk_eq_one] at h2
  exact ⟨h2.1, h2.2.1, h2.2.2⟩
end Formalism.TwoAdicCyclotomicDecomposition
