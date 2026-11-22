-- Prove2me | solution 1 for GES.isConf_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:48:12.441572+00:00
-- url     : https://prove2.me/submissions/f3bdcd51-324b-4537-addc-87568b48b91d

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
theorem _root_.solution {c : Set G.Event} (hc : G.isConf c) {x : G.Event} (hx : x ∈ c) :
    G.isConf ({z ∈ c | G.rank c z < G.rank c x} ∪ {x}) := by
  set m : Set G.Event := {z ∈ c | G.rank c z < G.rank c x} ∪ {x} with hm
  have hmc : m ⊆ c := by
    rintro z (hz | hz)
    · exact hz.1
    · exact (Set.mem_singleton_iff.mp hz) ▸ hx
  have hlt : ∀ {z}, z ∈ m → ∀ {g}, G.rank c g < G.rank c z → g ∈ c → g ∈ m := by
    rintro z (hz | hz) g hg hgc
    · exact Or.inl ⟨hgc, hg.trans hz.2⟩
    · exact Or.inl ⟨hgc, (Set.mem_singleton_iff.mp hz) ▸ hg⟩
  refine ⟨fun X hX => hc.1 X (hX.trans hmc), ?_⟩
  have key : ∀ n z, z ∈ m → G.rank c z = n → ∃ k, z ∈ G.secApprox m k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro z hz rfl
      obtain ⟨k, hk⟩ : ∃ k, G.rank c z = k + 1 := by
        have : G.rank c z ≠ 0 := by
          intro h0
          have hmem := rank_mem (hc.2 z (hmc hz))
          rw [h0] at hmem
          exact hmem
        exact ⟨G.rank c z - 1, by omega⟩
      obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem (hc.2 z (hmc hz))
      obtain ⟨N, hN⟩ := exists_bound (x := m) (X := X) fun g hg => by
        have hgc : g ∈ c := secApprox_subset _ (hXsub hg)
        have hglt : G.rank c g < G.rank c z := hk ▸ Nat.lt_succ_of_le (rank_le (hXsub hg))
        exact ih _ hglt g (hlt hz hglt hgc) rfl
      exact ⟨N + 1, hz, X, hN, hXen⟩
  exact fun z hz => key _ z hz rfl
end GES
