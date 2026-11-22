-- Prove2me | solution 1 for GES.isConf_insert_pmap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:38:33.727611+00:00
-- url     : https://prove2.me/submissions/53bb7b98-e912-4a29-9769-6712c0acc83a

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
    {c : Set G.Event} {u : G.Event} {x : H.Event} (hc : G.isConf c) (hφ : φ u = some x)
    (hcon : G.Consistent (c ∪ {u}))
    (hback : ∀ Y : Finset H.Event, (∀ y ∈ Y, y ∈ pmapSet φ c) → H.enable Y x →
      ∃ X : Finset G.Event, (X : Set G.Event) ⊆ c ∧ G.enable X u)
    (hx : H.isConf (pmapSet φ c ∪ {x})) : G.isConf (c ∪ {u}) := by
  refine ⟨hcon, ?_⟩
  have hmono : ∀ {v : G.Event}, v ∈ c → ∃ n, v ∈ G.secApprox (c ∪ {u}) n := by
    intro v hv
    obtain ⟨n, hn⟩ := hc.2 v hv
    exact ⟨n, secApprox_mono_set Set.subset_union_left n hn⟩
  rintro v (hv | hv)
  · exact hmono hv
  · replace hv : v = u := hv
    subst hv
    -- the enabling set of `x` avoids `x`, so it lies in the image of `c`
    obtain ⟨k, hk⟩ : ∃ k, H.rank (pmapSet φ c ∪ {x}) x = k + 1 := by
      have : H.rank (pmapSet φ c ∪ {x}) x ≠ 0 := by
        intro h0
        have hmem := rank_mem (hx.2 x (Or.inr rfl))
        rw [h0] at hmem
        exact hmem
      exact ⟨H.rank (pmapSet φ c ∪ {x}) x - 1, by omega⟩
    obtain ⟨-, Y, hYsub, hYen⟩ := hk ▸ rank_mem (hx.2 x (Or.inr rfl))
    have hYc : ∀ y ∈ Y, y ∈ pmapSet φ c := by
      intro y hy
      rcases secApprox_subset _ (hYsub hy) with h | h
      · exact h
      · exact absurd (hk ▸ Nat.lt_succ_of_le (rank_le (hYsub hy)) :
          H.rank (pmapSet φ c ∪ {x}) y < H.rank (pmapSet φ c ∪ {x}) x)
          (by rw [Set.mem_singleton_iff.mp h]; omega)
    obtain ⟨X, hXc, hXen⟩ := hback Y hYc hYen
    obtain ⟨N, hN⟩ := exists_bound (X := X) fun g hg => hmono (hXc (by exact_mod_cast hg))
    exact ⟨N + 1, Or.inr rfl, X, hN, hXen⟩
end GES
