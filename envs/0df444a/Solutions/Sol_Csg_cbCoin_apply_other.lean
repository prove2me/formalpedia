-- Prove2me | solution 1 for Csg.cbCoin_apply_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:12:41.554552+00:00
-- url     : https://prove2.me/submissions/6173049d-ae61-43ae-81d9-1214a982b850

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (x y z : CBState) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    cbCoin x y hxy z = 0 := by
  unfold cbCoin
  have hz : z ∉ ({x, y} : Finset CBState) := by simp [hzx, hzy]
  exact PMF.uniformOfFinset_apply_of_notMem ⟨x, by simp⟩ hz
end Csg
