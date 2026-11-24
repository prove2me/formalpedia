-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.star_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:33.646038+00:00
-- url     : https://prove2.me/submissions/8ffc0f96-661f-451f-81de-a649bd20127d

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
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U]
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution (b : 𝓞 E) : star (algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd E) b, rfl⟩
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
