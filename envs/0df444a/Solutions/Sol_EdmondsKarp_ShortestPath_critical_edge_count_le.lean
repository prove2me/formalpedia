-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.critical_edge_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:13:06.919977+00:00
-- url     : https://prove2.me/submissions/96e26b27-f159-4d14-ae85-d44d653ad105

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation
import Definitions.Def_EdmondsKarp_ShortestPath_Run

set_option autoImplicit false

theorem d27ff656_count_aux (g : ℕ → ℕ) (hm : Monotone g) (S : Finset ℕ)
    (hc : ∀ k ∈ S, g (k + 1) ≥ g k + 2) :
    ∀ j, (∀ x ∈ S, x < j) → 2 * S.card ≤ g j := by
  induction S using Finset.induction_on_max with
  | empty => intro j _; simp
  | insert a s hlt ih =>
    intro j hj
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.card_insert_of_notMem ha]
    have h1 : 2 * s.card ≤ g a :=
      ih (fun k hk => hc k (Finset.mem_insert_of_mem hk)) a hlt
    have h2 : g (a + 1) ≥ g a + 2 := hc a (Finset.mem_insert_self a s)
    have h3 : g (a + 1) ≤ g j := hm (hj a (Finset.mem_insert_self a s))
    omega

open EdmondsKarp.ShortestPath in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V)
    (hrun : IsShortestRun N K f P)
    (d : ℕ → V → ℕ) (C : V → V → Finset ℕ)
    (hmono : ∀ k v, d k v ≤ d (k + 1) v)
    (hcrit : ∀ u v k, k ∈ C u v → d (k + 1) u ≥ d k u + 2)
    (hbound : ∀ k v, d k v < Fintype.card V) :
    ∀ u v, (C u v).card ≤ (Fintype.card V - 1) / 2 := by
  intro u v
  have hm : Monotone (fun k => d k u) := monotone_nat_of_le_succ (fun k => hmono k u)
  have key := d27ff656_count_aux (fun k => d k u) hm (C u v)
    (fun k hk => hcrit u v k hk) ((C u v).sup id + 1)
    (fun x hx => Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))
  have hb := hbound ((C u v).sup id + 1) u
  omega
