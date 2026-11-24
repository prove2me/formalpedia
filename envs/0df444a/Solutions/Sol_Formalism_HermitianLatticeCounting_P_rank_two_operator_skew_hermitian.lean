-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.rank_two_operator_skew_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:43.536403+00:00
-- url     : https://prove2.me/submissions/e3281640-1954-4683-92ee-476edd1ac5a3

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms
open Finset Matrix
open scoped ComplexConjugate fwdDiff
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.RankTwoOperatorSkewHermitian := by
  intro V _ _ h hs e v x y
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul,
    RingHom.id_apply]
  rw [← hs y v, ← hs y e]
  ring
end Formalism.HermitianLatticeCounting.P
