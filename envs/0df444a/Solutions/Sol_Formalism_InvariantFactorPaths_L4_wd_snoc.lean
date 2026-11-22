-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wd_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:10.315242+00:00
-- url     : https://prove2.me/submissions/c82380d4-57d5-4100-bf00-4efa37dcec46

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
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (l : List (Fin r))
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    wd p LL j (l ++ [c]) F = wd p LL j l (glAct p LL j 0 c F) := by
  simp only [wd, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, Module.End.mul_apply]
end Formalism.InvariantFactorPaths.L4
