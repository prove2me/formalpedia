-- Prove2me | solution 1 for Erdos146.BinaryPairKernel.averageDisagreement_eq_four_outcomes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:02:33.214058+00:00
-- url     : https://prove2.me/submissions/b3ae0443-508f-4efa-95eb-aeac1dca5a4e

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (kernel : BinaryPairKernel) :
    kernel.averageDisagreement =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        kernel.parentProbability * (1 - kernel.parentProbability) +
        kernel.parentProbability ^ 2 *
          (1 - kernel.childProbability true true) := by
  simp [averageDisagreement, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass,
    bitDisagreementProbability]
  ring
