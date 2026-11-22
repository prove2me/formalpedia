-- Prove2me | solution 1 for Comp.CsgQ.toPMF_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:36:49.692807+00:00
-- url     : https://prove2.me/submissions/352ab2e3-a6f3-4290-b31f-00c838e03bcb

import Definitions.Def_Csg_Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Comp_Basic

set_option autoImplicit true
open Comp
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Comp.CsgQ
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    (G.toPMF h s a1 a2 s').toReal = ((G.K s a1 a2 s' : ℚ) : ℝ) := by
  unfold toPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (K_cast_nonneg h s a1 a2 s')
end Comp.CsgQ
