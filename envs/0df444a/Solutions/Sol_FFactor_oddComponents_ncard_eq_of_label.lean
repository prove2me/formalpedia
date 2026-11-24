-- Prove2me | solution 1 for FFactor.oddComponents_ncard_eq_of_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:53:15.6468+00:00
-- url     : https://prove2.me/submissions/ccd536d5-843f-4914-8851-cbecd5e41810

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Theorems.Thm_FFactor_label_eq_of_reachable

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {X L : Type*} (H : SimpleGraph X) (φ : X → L)
open Classical
namespace FFactor
theorem _root_.solution [Fintype X]
    (h1 : ∀ x y, H.Adj x y → φ x = φ y) (h2 : ∀ x y, φ x = φ y → H.Reachable x y) :
    H.oddComponents.ncard = #{l ∈ univ.image φ | Odd #{x | φ x = l}} := by
  let ψ : H.ConnectedComponent → L :=
    ConnectedComponent.lift φ (fun v w p _ => label_eq_of_reachable H φ h1 ⟨p⟩)
  have hψ : ∀ x, ψ (H.connectedComponentMk x) = φ x := fun x => rfl
  have hinj : Function.Injective ψ := by
    intro c d hcd
    induction c using ConnectedComponent.ind with | h x => ?_
    induction d using ConnectedComponent.ind with | h y => ?_
    exact ConnectedComponent.sound (h2 x y hcd)
  have hsupp : ∀ c : H.ConnectedComponent, c.supp = {x | φ x = ψ c} := by
    intro c
    induction c using ConnectedComponent.ind with | h y => ?_
    ext x
    simp only [ConnectedComponent.mem_supp_iff, Set.mem_ofPred_eq, hψ]
    constructor
    · intro h; rw [← hψ, ← hψ, h]
    · intro h; exact ConnectedComponent.sound (h2 x y h)
  have key : ∀ l, ({x | φ x = l} : Set X).ncard = #{x | φ x = l} := fun l => by
    rw [← Set.ncard_coe_finset]; simp
  rw [← Set.ncard_image_of_injective _ hinj, ← Set.ncard_coe_finset]
  congr 1
  ext l
  simp only [Set.mem_image, Set.mem_ofPred_eq, coe_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩
    induction c using ConnectedComponent.ind with | h y => ?_
    refine ⟨⟨y, rfl⟩, ?_⟩
    rw [hsupp, key] at hc
    exact hc
  · rintro ⟨⟨y, rfl⟩, hodd⟩
    refine ⟨H.connectedComponentMk y, ?_, rfl⟩
    show Odd (H.connectedComponentMk y).supp.ncard
    rw [hsupp, key]
    exact hodd
end FFactor
