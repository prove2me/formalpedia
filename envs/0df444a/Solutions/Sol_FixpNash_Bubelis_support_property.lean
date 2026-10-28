-- Prove2me | solution 1 for FixpNash.Bubelis.support_property
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:57:25.031243+00:00
-- url     : https://prove2.me/submissions/4395db37-ff28-4b3b-86ba-537788dec429

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Theorems.Thm_FixpNash_Blocks_support_property


/-- Support property of a mixed Nash equilibrium (proof of Lemma 7, p. 26): in a Nash
equilibrium `x` of a finite game, the expected payoff `u_p((p:j); x_{-p})` of every pure strategy
`j` of player `p` is at most `p`'s equilibrium payoff `u_p(x)`, with equality when `j` is in the
support of `x_p`. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedNash u x)
    (p : ι) (j : S p) :
    DGPNash.NashMap.purePayoff u x p j ≤ AGT.expectedPayoff u x p ∧
      (0 < x p j → DGPNash.NashMap.purePayoff u x p j = AGT.expectedPayoff u x p) := by
  apply FixpNash.Blocks.support_property <;> assumption


