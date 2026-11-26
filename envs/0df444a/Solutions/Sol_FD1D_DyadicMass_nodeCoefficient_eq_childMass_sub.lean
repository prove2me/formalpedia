-- Prove2me | solution 1 for FD1D.DyadicMass.nodeCoefficient_eq_childMass_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:53.274602+00:00
-- url     : https://prove2.me/submissions/a3b4798f-184f-46eb-b23c-899261e7ba68

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (q : DyadicMass L)
    (v : CompleteHaarNode L) :
    q.nodeCoefficient v =
      (q.nodeChildMasses v).1 - (q.nodeChildMasses v).2 :=
  rfl
end FD1D.DyadicMass
