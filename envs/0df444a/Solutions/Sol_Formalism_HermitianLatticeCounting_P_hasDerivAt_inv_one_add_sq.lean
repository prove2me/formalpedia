-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hasDerivAt_inv_one_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:29.86518+00:00
-- url     : https://prove2.me/submissions/6e49f2e1-b1d3-4d92-b927-066faf8b2fcc

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (y : ℝ) :
    HasDerivAt (fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹) (y * ((1 + y ^ 2) ^ 2)⁻¹) y := by
  have hpos : (1 + y ^ 2) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
    simpa using ((hasDerivAt_id y).pow 2).const_add 1
  have h2 := (h1.inv hpos).const_mul (-(1 / 2) : ℝ)
  have e : y * ((1 + y ^ 2) ^ 2)⁻¹ = -(1 / 2) * (-(2 * y) / (1 + y ^ 2) ^ 2) := by
    rw [div_eq_mul_inv]
    ring
  rw [e]
  exact h2
end Formalism.HermitianLatticeCounting.P
