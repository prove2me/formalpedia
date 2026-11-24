-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gainExponent_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:20.554502+00:00
-- url     : https://prove2.me/submissions/28557bff-b7a1-4097-98bb-937304c1e25a

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
theorem _root_.solution (k r : ℕ) : 0 ≤ expo k r := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
end Formalism.HermitianLatticeCounting.P
