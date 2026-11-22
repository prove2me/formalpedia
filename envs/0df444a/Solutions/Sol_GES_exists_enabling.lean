-- Prove2me | solution 1 for GES.exists_enabling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:40:28.623979+00:00
-- url     : https://prove2.me/submissions/ef4363fd-f73e-440d-ad54-df3a4b3ce32b

import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Minimal
import Definitions.Def_EventStructures_General_Basic

set_option autoImplicit true
open GES
variable {L : Type*} (G : GES L)
local infix:50 " ⊢ " => G.enable
variable {G}
variable (G)
variable {G}
namespace GES
theorem _root_.solution {x : Set G.Event} (hx : G.isConf x) {e : G.Event} (he : e ∈ x) :
    ∃ Y : Finset G.Event, (Y ⊢ e) ∧ ↑Y ⊆ x := by
  obtain ⟨n, hn⟩ := hx.2 e he
  cases n with
  | zero => exact hn.elim
  | succ k =>
    obtain ⟨-, Y, hYsub, hYen⟩ := hn
    exact ⟨Y, hYen, hYsub.trans (secApprox_subset k)⟩
end GES
