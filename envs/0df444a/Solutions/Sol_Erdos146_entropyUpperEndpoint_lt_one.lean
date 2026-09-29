-- Prove2me | solution 1 for Erdos146.entropyUpperEndpoint_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:08:56.364138+00:00
-- url     : https://prove2.me/submissions/992d7834-bb1f-4e6c-9ed6-06dad3bf424b

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Theorems.Thm_Erdos146_tau_lt_one_half

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem binaryEntropy_tau_lt_one : binaryEntropy tau < 1 := by
  have htau_ne : tau ≠ (2 : ℝ)⁻¹ := by
    intro heq
    have hlt := tau_lt_one_half
    rw [heq] at hlt
    norm_num at hlt
  unfold binaryEntropy
  apply (div_lt_iff₀ log_two_pos).mpr
  simpa using (Real.binEntropy_lt_log_two.mpr htau_ne)

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution : entropyUpperEndpoint < 1 := by
  unfold entropyUpperEndpoint
  nlinarith [binaryEntropy_tau_lt_one]
