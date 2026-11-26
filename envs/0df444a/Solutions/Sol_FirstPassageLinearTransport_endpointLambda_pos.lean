-- Prove2me | solution 1 for FirstPassageLinearTransport.endpointLambda_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:23:23.471512+00:00
-- url     : https://prove2.me/submissions/c01abb63-576a-47de-9431-6e72690baf48

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) : 0 < endpointLambda n := by
  unfold endpointLambda
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hden : (1 : ℝ) < (n : ℝ) + 2 := by linarith
  have hinv : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by positivity)).2 hden
  linarith
end FirstPassageLinearTransport
