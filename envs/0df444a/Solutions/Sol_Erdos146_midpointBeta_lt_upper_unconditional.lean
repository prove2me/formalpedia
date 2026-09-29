-- Prove2me | solution 1 for Erdos146.midpointBeta_lt_upper_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:08:14.889737+00:00
-- url     : https://prove2.me/submissions/e31b2bb2-efeb-4145-a587-4fa7a84e4f8f

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem midpointBeta_lt_upper
    (hwindow : entropyLowerEndpoint < entropyUpperEndpoint) :
    midpointBeta < entropyUpperEndpoint := by
  unfold midpointBeta
  linarith

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution :
    midpointBeta < entropyUpperEndpoint :=
  midpointBeta_lt_upper entropyWindow_pos
