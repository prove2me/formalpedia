-- Prove2me | solution 1 for Csg.cbT3_payoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:15.763271+00:00
-- url     : https://prove2.me/submissions/e7ce12c8-b046-483c-9625-a7b1d2a167de

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_rowMove_sum
import Theorems.Thm_Csg_colMove_sum
import Theorems.Thm_Csg_cbT3A

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) (p : RowMove → ℝ) (q : ColMove → ℝ)
    (hp : p ∈ stdSimplex ℝ RowMove) :
    (cbCSG.stageGame .t3 v).payoff p q = q .c * v .t3 + q .d * ((v .t2 + v .t4) / 2) := by
  rw [MatrixGame.payoff_eq_sum_mul', colMove_sum]
  have hc : ∑ i, p i * (cbCSG.stageGame .t3 v).A i .c = v .t3 := by
    have : ∀ i, p i * (cbCSG.stageGame .t3 v).A i .c = p i * v .t3 := fun i => by
      rw [cbT3A]; simp
    rw [rowMove_sum, this .b, this .d, ← add_mul, ← rowMove_sum p, hp.2, one_mul]
  have hd : ∑ i, p i * (cbCSG.stageGame .t3 v).A i .d = (v .t2 + v .t4) / 2 := by
    have : ∀ i, p i * (cbCSG.stageGame .t3 v).A i .d = p i * ((v .t2 + v .t4) / 2) := fun i => by
      rw [cbT3A]; simp
    rw [rowMove_sum, this .b, this .d, ← add_mul, ← rowMove_sum p, hp.2, one_mul]
  rw [hc, hd]; ring
end Csg
