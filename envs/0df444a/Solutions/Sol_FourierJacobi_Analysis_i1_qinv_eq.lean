-- Prove2me | solution 1 for FourierJacobi.Analysis.i1_qinv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:04.138308+00:00
-- url     : https://prove2.me/submissions/59bda00d-388e-421c-b797-9a23ac2cce97

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t : ℂ) (ht : t ≠ 0) (hqt : q * t ^ 2 = 1) :
    q⁻¹ = t ^ 2 := by
  have he : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hqt, one_mul]
  rw [he, inv_inv]
end FourierJacobi.Analysis
