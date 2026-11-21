-- Prove2me | solution 1 for Cage87.verticesOk_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:18:34.509626+00:00
-- url     : https://prove2.me/submissions/c002b636-db7f-4945-86f4-ae99b8a836e8

module
public import Definitions.Def_Cage87_Check

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution (adj : Trie) : ∀ (lo c : Nat), verticesOk adj lo c = true →
    ∀ v, lo ≤ v → v < lo + c → vertexOk adj v = true := by
  intro lo c
  induction c generalizing lo with
  | zero => intro _ v h1 h2; omega
  | succ c ih =>
    intro h v h1 h2
    simp only [verticesOk, Bool.and_eq_true] at h
    by_cases hv : v = lo
    · exact hv ▸ h.1
    · exact ih (lo + 1) h.2 v (by omega) (by omega)
end Cage87
