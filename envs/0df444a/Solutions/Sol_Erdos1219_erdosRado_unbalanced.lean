-- Prove2me | solution 1 for Erdos1219.erdosRado_unbalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:47:37.891611+00:00
-- url     : https://prove2.me/submissions/ca8c6800-4de4-416a-b491-b9c87aed1b3a

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Theorems.Thm_Erdos1219_erdosRado_unbalanced_wo

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (C : Set V) (hC : #C = Order.succ (2 ^ μ)) (c : Bool) :
    (∃ H ⊆ C, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H ⊆ C, #H = Order.succ μ ∧ Homog f (!c) H) := by
  have hW : #((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) = Order.succ (2 ^ μ) :=
    mk_ord_toType _
  have hord : ord #((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) =
      typeLT ((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) := by
    rw [hW, type_toType]
  obtain ⟨e⟩ : Nonempty (C ≃ (Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) :=
    Cardinal.eq.1 (hC.trans hW.symm)
  let g : (Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType → V := fun x => (e.symm x : V)
  have hg : Function.Injective g := fun x y hxy =>
    e.symm.injective (Subtype.val_injective hxy)
  have hf' : ∀ x y, f (g x) (g y) = f (g y) (g x) := fun x y => hf _ _
  have transport : ∀ (d : Bool) (H : Set ((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType)),
      Homog (fun x y => f (g x) (g y)) d H →
        g '' H ⊆ C ∧ #(g '' H) = #H ∧ Homog f d (g '' H) := by
    intro d H hH
    refine ⟨?_, mk_image_eq hg, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact (e.symm x).2
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hH x hx y hy fun h => hxy (congrArg g h)
  rcases erdosRado_unbalanced_wo hf' hμ hW hord c with ⟨H, hH, hHc⟩ | ⟨H, hH, hHc⟩
  · obtain ⟨h1, h2, h3⟩ := transport c H hHc
    exact Or.inl ⟨g '' H, h1, h2.trans hH, h3⟩
  · obtain ⟨h1, h2, h3⟩ := transport (!c) H hHc
    exact Or.inr ⟨g '' H, h1, h2.trans hH, h3⟩
end Erdos1219
