-- Prove2me | solution 1 for Erdos1219.exists_seq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:25.115797+00:00
-- url     : https://prove2.me/submissions/353042ef-0024-48aa-ba7a-705c234c6801

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {X : Type u} [LinearOrder X] [WellFoundedLT X]
namespace Erdos1219
theorem _root_.solution {I W : Type u} [LinearOrder I] [WellFoundedLT I] [LinearOrder W]
    [WellFoundedLT W] {κ : Cardinal.{u}}
    (hb : ∀ s : Set W, #s < κ → ∃ x, ∀ y ∈ s, y < x) (hI : ∀ ξ : I, #(Iio ξ) < κ)
    (h : W → W) : ∃ β : I → W, ∀ ξ η, η < ξ → h (β η) < β ξ := by
  let F : (ξ : I) → ((η : I) → η < ξ → W) → W := fun ξ IH =>
    Classical.choose (hb (range fun η : Iio ξ => h (IH η η.2)) (mk_range_le.trans_lt (hI ξ)))
  refine ⟨WellFounded.fix wellFounded_lt F, fun ξ η hη => ?_⟩
  rw [WellFounded.fix_eq wellFounded_lt F ξ]
  exact Classical.choose_spec
    (hb (range fun η : Iio ξ => h (WellFounded.fix wellFounded_lt F η))
      (mk_range_le.trans_lt (hI ξ))) _ ⟨⟨η, hη⟩, rfl⟩
end Erdos1219
