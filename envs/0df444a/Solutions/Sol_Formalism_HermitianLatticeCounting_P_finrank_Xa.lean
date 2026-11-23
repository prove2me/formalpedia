-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.finrank_Xa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:24.229617+00:00
-- url     : https://prove2.me/submissions/edc18ab8-1267-4175-b007-5529cf4c69f0

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_eq_range
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_indep_le

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
theorem _root_.solution (F : FlagD H r) {j : ℕ} (hj : j ≤ r) : Module.finrank K (F.Xa j) = j := by
  rw [(Xa_eq_range F) hj, finrank_span_eq_card ((indep_le F) hj), Fintype.card_fin]
end Formalism.HermitianLatticeCounting.P
