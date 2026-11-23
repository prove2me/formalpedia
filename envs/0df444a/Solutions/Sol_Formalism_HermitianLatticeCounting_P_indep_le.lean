-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.indep_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:32.222604+00:00
-- url     : https://prove2.me/submissions/b5c01e84-748c-4371-a42b-8e1c926731f5

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow

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
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (F : FlagD H r) {j : ℕ} (hj : j ≤ r) :
    LinearIndependent K (fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) := by
  have := F.indep.comp (Fin.castLE hj) (Fin.castLE_injective hj)
  exact this
end Formalism.HermitianLatticeCounting.P
