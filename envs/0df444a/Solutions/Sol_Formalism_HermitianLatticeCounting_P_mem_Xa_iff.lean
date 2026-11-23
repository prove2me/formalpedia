-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.mem_Xa_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:17.502512+00:00
-- url     : https://prove2.me/submissions/9384b574-337a-457e-a487-f7e28403fbbb

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_eq_range

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
theorem _root_.solution (F : FlagD H r) {j : ℕ} (hj : j ≤ r) {x : V} :
    x ∈ F.Xa j ↔ ∃ c : Fin j → K, ∑ a, c a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) = x := by
  rw [(Xa_eq_range F) hj, Submodule.mem_span_range_iff_exists_fun]
end Formalism.HermitianLatticeCounting.P
