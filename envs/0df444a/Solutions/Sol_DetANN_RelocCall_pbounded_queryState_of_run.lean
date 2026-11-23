-- Prove2me | solution 1 for DetANN.RelocCall.pbounded_queryState_of_run
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:34.340593+00:00
-- url     : https://prove2.me/submissions/d6c7f2fc-3138-4473-899b-fc08a6904d97

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Theorems.Thm_PNormRegLib_bounded_run
import Theorems.Thm_DetANN_pbounded_inputState
import Theorems.Thm_DetANN_pbounded_queryState

open PNormReg PNormRegLib DetANN in
/-- If `X` bounds both the literals of `Pre` and its input state, then after `t` preprocessing steps,
the standard start state of every query on the resulting memory is `X * 2^t`-bounded. -/
theorem solution {N m : ℕ}
    (Y : Fin N → EuclideanSpace ℝ (Fin m)) (θ : ℝ)
    (Pre : Program) (X : ℤ) (hlit : LitBound Pre X) (hX : 1 ≤ X)
    (hNX : (N : ℤ) + m + 1 ≤ X) (t : ℕ) (q : EuclideanSpace ℝ (Fin m)) :
    PBounded (X * 2 ^ t) (queryState m (run Pre (inputState Y θ) detTape t) q) := by
  have hinput : PBounded X (inputState Y θ) := by
    have h := pbounded_inputState Y θ
    exact ⟨fun u => (h.1 u).trans hNX, fun z => (h.2 z).trans hNX⟩
  have hrun : PBounded (X * 2 ^ t) (run Pre (inputState Y θ) detTape t) :=
    bounded_run Pre detTape X (inputState Y θ) hinput hlit hX t
  exact pbounded_queryState (X * 2 ^ t) _ hrun (by positivity) m q
