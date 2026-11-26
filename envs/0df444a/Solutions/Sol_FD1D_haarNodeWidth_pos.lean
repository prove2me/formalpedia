-- Prove2me | solution 1 for FD1D.haarNodeWidth_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:20.732583+00:00
-- url     : https://prove2.me/submissions/ea823182-c974-439a-a62b-6b6508c081cd

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution {L : ℕ} (v : CompleteHaarNode L) :
    0 < haarNodeWidth v := by
  simp [haarNodeWidth]
end FD1D
