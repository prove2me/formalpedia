-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integral_norm_estimate_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:49.836315+00:00
-- url     : https://prove2.me/submissions/a0e8f19d-e5c3-44f2-9cf2-97fa7a9e6315

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.AlgebraicIntegerNormGeOne := by
  intro E _ _ x hx
  rw [InfinitePlace.prod_eq_abs_norm]
  have h : (Algebra.norm ℤ x) ≠ 0 := by
    simpa [Algebra.norm_eq_zero_iff] using hx
  have h2 : (Algebra.norm ℚ (x : E)) = ((Algebra.norm ℤ x : ℤ) : ℚ) := by
    rw [Algebra.coe_norm_int]
  rw [h2]
  have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs h
  exact_mod_cast this
end Formalism.HermitianLatticeCounting.P
