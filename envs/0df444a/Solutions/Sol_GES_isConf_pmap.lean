-- Prove2me | solution 1 for GES.isConf_pmap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:37:38.2478+00:00
-- url     : https://prove2.me/submissions/80616514-b1c3-46dd-92b5-4e532a2488fd

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
variable (G)
namespace GES
theorem _root_.solution {L' : Type*} {G : GES L} {H : GES L'}
    (φ : G.Event → Option H.Event)
    (hcon : ∀ {c : Set G.Event}, G.Consistent c → H.Consistent (pmapSet φ c))
    (hen : ∀ {X : Finset G.Event} {u : G.Event} {x : H.Event},
      G.enable X u → φ u = some x →
      ∃ Y : Finset H.Event, (∀ y ∈ Y, y ∈ pmapSet φ (X : Set G.Event)) ∧ H.enable Y x)
    {c : Set G.Event} (hc : G.isConf c) : H.isConf (pmapSet φ c) := by
  refine ⟨hcon hc.1, ?_⟩
  have key : ∀ n u, u ∈ c → G.rank c u = n →
      ∀ x, φ u = some x → ∃ m, x ∈ H.secApprox (pmapSet φ c) m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro u hu rfl x hx
      obtain ⟨k, hk⟩ : ∃ k, G.rank c u = k + 1 := by
        have : G.rank c u ≠ 0 := by
          intro h0
          have hmem := rank_mem (hc.2 u hu)
          rw [h0] at hmem
          exact hmem
        exact ⟨G.rank c u - 1, by omega⟩
      obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem (hc.2 u hu)
      obtain ⟨Y, hY, hYen⟩ := hen hXen hx
      obtain ⟨N, hN⟩ := exists_bound (x := pmapSet φ c) (X := Y) fun y hy => by
        obtain ⟨v, hv, hev⟩ := hY y hy
        have hvc : v ∈ c := secApprox_subset _ (hXsub hv)
        refine ih _ ?_ v hvc rfl y hev
        exact hk ▸ Nat.lt_succ_of_le (rank_le (hXsub hv))
      exact ⟨N + 1, ⟨u, hu, hx⟩, Y, hN, hYen⟩
  rintro x ⟨u, hu, hx⟩
  exact key _ u hu rfl x hx
end GES
