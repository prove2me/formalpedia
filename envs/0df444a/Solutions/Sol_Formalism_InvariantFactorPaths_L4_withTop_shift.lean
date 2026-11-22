-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.withTop_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:33.467073+00:00
-- url     : https://prove2.me/submissions/929ffe04-0ff0-4cb6-a3ba-2fe6820ad735

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (w : ℤ) (M : WithTop ℤ) :
    ((w + 1 : ℤ) : WithTop ℤ) ≤ M ↔ ((w : ℤ) : WithTop ℤ) ≤ M + ((-1 : ℤ) : WithTop ℤ) := by
  induction M using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    omega
end Formalism.InvariantFactorPaths.L4
