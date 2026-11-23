-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_finrank_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:21.651295+00:00
-- url     : https://prove2.me/submissions/4c166a5a-a7cb-48ea-830c-58dcd0b20433

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (n : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).finrank_eq, Module.finrank_pi_fintype]
  simp [mul_comm]
end Formalism.HermitianLatticeCounting.P
