-- Prove2me | solution 1 for GJKKL.bnd_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:44:01.255925+00:00
-- url     : https://prove2.me/submissions/a65bdf54-e768-4565-9042-73f5eb96f8b1

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (k : ℕ) (dh δ : ℕ → ℝ) (t : ℕ) :
    bnd V k dh δ t = ((k : ℝ) - 1) * (dh t + δ t) ^ 2 / (aPar V k t * (dh t - δ t)) +
      ((dh t - dh (t + 1)) + (δ (t + 1) - δ t)) := rfl
end GJKKL
