-- Prove2me | solution 1 for Csg.cbT2_payoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:04.034557+00:00
-- url     : https://prove2.me/submissions/56c55993-c3a7-42d3-a392-ef8ef486fb18

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_rowMove_sum
import Theorems.Thm_Csg_colMove_sum
import Theorems.Thm_Csg_cbT2A

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) (p : RowMove → ℝ) (q : ColMove → ℝ)
    (hq : q ∈ stdSimplex ℝ ColMove) :
    (cbCSG.stageGame .t2 v).payoff p q = p .b * v .t2 + p .d * ((v .t1 + v .t3) / 2) := by
  rw [MatrixGame.payoff_eq_sum_mul, rowMove_sum]
  have hb : ∑ j, (cbCSG.stageGame .t2 v).A .b j * q j = v .t2 := by
    have : ∀ j, (cbCSG.stageGame .t2 v).A .b j * q j = v .t2 * q j := fun j => by
      rw [cbT2A]; simp
    rw [colMove_sum, this .c, this .d, ← mul_add, ← colMove_sum q, hq.2, mul_one]
  have hd : ∑ j, (cbCSG.stageGame .t2 v).A .d j * q j = (v .t1 + v .t3) / 2 := by
    have : ∀ j, (cbCSG.stageGame .t2 v).A .d j * q j = (v .t1 + v .t3) / 2 * q j := fun j => by
      rw [cbT2A]; simp
    rw [colMove_sum, this .c, this .d, ← mul_add, ← colMove_sum q, hq.2, mul_one]
  rw [hb, hd]
end Csg
