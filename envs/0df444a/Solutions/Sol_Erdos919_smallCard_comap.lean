-- Prove2me | solution 1 for Erdos919.smallCard_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:13:49.500738+00:00
-- url     : https://prove2.me/submissions/a658ba87-b535-40d4-9fa6-749396fe1715

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V V' : Type u} (e : V ≃ V') {G : SimpleGraph V'}
    (hG : SmallCardCC G) : SmallCardCC (G.comap e) := by
  intro X hX
  obtain ⟨c, hc⟩ := hG (e '' X) (mk_image_le.trans hX)
  exact ⟨c ∘ e, fun x hx y hy hxy => hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy⟩
end Erdos919
