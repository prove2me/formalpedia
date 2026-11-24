-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.omega_mul_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:14.49595+00:00
-- url     : https://prove2.me/submissions/0b94cc40-9d45-44f4-bcaf-5c24a4711767

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution {q n' : ℕ} (hq : 1 < q) (hn' : 1 ≤ n') :
    1 + (Nat.primeFactorsList n').length ≤ (Nat.primeFactorsList (q * n')).length := by
  rw [(Nat.perm_primeFactorsList_mul (by omega) (by omega)).length_eq, List.length_append]
  have : 0 < (Nat.primeFactorsList q).length := by
    rw [List.length_pos_iff, Nat.primeFactorsList_ne_nil]
    exact hq
  omega
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
