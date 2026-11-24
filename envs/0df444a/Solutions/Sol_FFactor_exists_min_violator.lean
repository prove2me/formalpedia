-- Prove2me | solution 1 for FFactor.exists_min_violator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:02:46.165168+00:00
-- url     : https://prove2.me/submissions/1935a989-8817-4017-b3b1-e11656d29adb

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Theorems.Thm_FFactor_ncard_oddComponents_del_le

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {W : Type*} (Γ : SimpleGraph W)
namespace FFactor
theorem _root_.solution [Finite W] (h : ∃ U, Γ.IsTutteViolator U) :
    ∃ U, Γ.IsTutteViolator U ∧ ∀ x ∈ U, ¬ TwoComp Γ U x := by
  classical
  have hex : ∃ n, ∃ U, U.ncard = n ∧ Γ.IsTutteViolator U := by
    obtain ⟨U, hU⟩ := h; exact ⟨_, U, rfl, hU⟩
  obtain ⟨U, hUn, hU⟩ := Nat.find_spec hex
  refine ⟨U, hU, fun x hx htwo => ?_⟩
  have hle := ncard_oddComponents_del_le Γ U x hx htwo
  have hcard : (U \ {x}).ncard + 1 = U.ncard := Set.ncard_sdiff_singleton_add_one hx
  have hviol : Γ.IsTutteViolator (U \ {x}) := by
    unfold IsTutteViolator at hU ⊢
    change U.ncard < (del Γ U).oddComponents.ncard at hU
    change (U \ {x}).ncard < (del Γ (U \ {x})).oddComponents.ncard
    omega
  have := Nat.find_min' hex ⟨U \ {x}, rfl, hviol⟩
  omega
end FFactor
