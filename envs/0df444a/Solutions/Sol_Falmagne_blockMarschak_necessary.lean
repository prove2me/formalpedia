-- Prove2me | solution 1 for Falmagne.blockMarschak_necessary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:41.631798+00:00
-- url     : https://prove2.me/submissions/18ad6bcd-87c7-40f3-8147-5d936156cab1

module
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Theorems.Thm_Falmagne_mobius_eq_lawFlow
public import Theorems.Thm_Falmagne_lawFlow_nonneg


set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : IsRankingLaw w) (hp : Represents w p) :
    ∀ x A, x ∈ A → 0 ≤ upperMobius (fun B => p B x) A := by
  intro x A hx
  rw [mobius_eq_lawFlow hw.2.1 hp x A hx]
  exact lawFlow_nonneg hw.1 x A
end Falmagne
