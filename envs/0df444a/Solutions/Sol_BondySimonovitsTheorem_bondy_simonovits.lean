-- Prove2me | solution 1 for BondySimonovitsTheorem.bondy_simonovits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:21:51.418222+00:00
-- url     : https://prove2.me/submissions/f0961298-7b9b-4e79-965f-72fb33a6c455

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BondySimonovits
public import Definitions.Def_BondySimonovitsLib_Solution
public import Theorems.Thm_BondySimonovits_bondy_simonovits


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BondySimonovitsTheorem
universe u
namespace BondySimonovitsTheorem
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≠ 2 * k) →
      (G.edgeSet.ncard : ℝ) ≤ C * (Nat.card V : ℝ) ^ (1 + 1 / (k : ℝ)) :=
  BondySimonovits.bondy_simonovits k hk
end BondySimonovitsTheorem
