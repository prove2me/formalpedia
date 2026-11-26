-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.average_pow_sourceCodeOddCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:44.363904+00:00
-- url     : https://prove2.me/submissions/642f599c-c2e8-40a5-94b9-f748adc87028

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_pow_sourceCodeOddCount

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (q : ℝ) :
    (∑ x : SourceCode M, q ^ sourceCodeOddCount x) /
        (2 ^ M : ℝ) =
      ((1 + q) / 2) ^ M := by
  rw [sum_pow_sourceCodeOddCount]
  rw [div_pow]
end CollatzEndpointTransport.FixedTotal
