-- Prove2me | solution 1 for Csg.cbCoin_apply_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:12:41.140607+00:00
-- url     : https://prove2.me/submissions/c65d4f11-cd82-4709-be6f-24da4e5b3292

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (x y : CBState) (hxy : x ≠ y) :
    cbCoin x y hxy y = (2 : ENNReal)⁻¹ := by
  unfold cbCoin
  have hy : y ∈ ({x, y} : Finset CBState) := by simp
  rw [PMF.uniformOfFinset_apply_of_mem ⟨x, by simp⟩ hy, Finset.card_pair hxy]
  norm_num
end Csg
