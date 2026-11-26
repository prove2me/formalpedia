-- Prove2me | solution 1 for FD1D.DyadicMass.haarNodeLeft_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:37.734628+00:00
-- url     : https://prove2.me/submissions/29faaa97-fd54-4e28-bf17-bee77c9ffd9f

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
    0 ≤ haarNodeLeft v := by
  unfold haarNodeLeft
  positivity
end FD1D.DyadicMass
