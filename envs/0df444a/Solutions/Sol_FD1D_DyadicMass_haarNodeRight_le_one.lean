-- Prove2me | solution 1 for FD1D.DyadicMass.haarNodeRight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:44.631079+00:00
-- url     : https://prove2.me/submissions/2665ed46-e6cb-4147-9482-b0a607d437e4

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeLeft v + haarNodeWidth v ≤ 1 := by
  unfold haarNodeLeft haarNodeWidth
  have hp : (0 : ℝ) < (2 ^ v.1.val : ℕ) := by positivity
  rw [← add_div]
  apply (div_le_one hp).2
  norm_cast
  omega
end FD1D.DyadicMass
