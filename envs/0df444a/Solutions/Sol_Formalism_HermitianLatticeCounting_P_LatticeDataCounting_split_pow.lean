-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.split_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:17.262732+00:00
-- url     : https://prove2.me/submissions/8d4a9a0c-6a44-4951-9814-22f5539fe3ba

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting

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
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution (i' : ℝ) (hi : 1 ≤ i') (k : ℕ) (c : ℝ) : i' ^ ((k : ℝ) + c) = i' ^ k * i' ^ c := by
  rw [Real.rpow_add (by linarith), Real.rpow_natCast]
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
