-- Prove2me | solution 1 for FD1D.DyadicMass.exists_monotoneQuantilePolicy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:59.863+00:00
-- url     : https://prove2.me/submissions/78d8ee57-51f0-4a6b-8ecd-297963e7d618

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
namespace DyadicMass
theorem _root_.solution {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) :
    ∃ P : MonotoneQuantilePolicy q.piecewiseCDF,
      P.withinError = 1 / ((2 ^ L : ℕ) : ℝ) :=
  ⟨q.quantilePolicy hq, rfl⟩
end DyadicMass
end FD1D
