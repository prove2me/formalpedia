-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.vsph_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:08.451795+00:00
-- url     : https://prove2.me/submissions/d630a5d9-9561-45c7-aaeb-21798bf9b4ad

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (k J : ℕ) : Vsph (k + J)
    = Vsph k * ∏ i ∈ range J, (2 * Real.pi ^ (k + i + 1) / ((k + i).factorial : ℝ)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
    unfold Vsph
    rw [← add_assoc, Finset.prod_Icc_succ_top (by omega)]
    simp
end Formalism.HermitianLatticeCounting.P
