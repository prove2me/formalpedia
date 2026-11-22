-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.heightParameter_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:26.022183+00:00
-- url     : https://prove2.me/submissions/3906743a-fdbb-440f-8cc4-1a9149701ffe

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (C : ℝ) (m f : ℕ) (b y : ℝ) (hb : 0 < b) :
    bigH C m f b ^ y = Real.exp ((C * (m:ℝ) ^ 2 * f * Real.log b) * y) := by
  unfold bigH
  rw [← Real.rpow_mul hb.le, Real.rpow_def_of_pos hb]
  congr 1
  ring
end Formalism.HermitianLatticeCounting.P
