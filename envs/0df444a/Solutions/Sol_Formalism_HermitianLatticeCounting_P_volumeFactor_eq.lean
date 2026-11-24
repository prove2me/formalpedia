-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.volumeFactor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:42.189159+00:00
-- url     : https://prove2.me/submissions/18800378-30f8-4a46-9a1c-6f35b875356b

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

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
theorem _root_.solution (k r : ℕ) (G T g v : ℝ) :
    nv k r G T g v =
      (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nv
  rw [← mul_pow, ← mul_pow]
  congr 1
  ring
end Formalism.HermitianLatticeCounting.P
