-- Prove2me | solution 1 for Csg.cbCoin_apply_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:12:33.076273+00:00
-- url     : https://prove2.me/submissions/6f34091c-fe62-48b9-930d-828cc9df2f7b

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
    cbCoin x y hxy x = (2 : ENNReal)⁻¹ := by
  unfold cbCoin
  have hx : x ∈ ({x, y} : Finset CBState) := by simp
  rw [PMF.uniformOfFinset_apply_of_mem ⟨x, by simp⟩ hx, Finset.card_pair hxy]
  norm_num
end Csg
