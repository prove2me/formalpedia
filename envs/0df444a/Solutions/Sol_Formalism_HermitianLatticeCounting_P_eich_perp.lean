-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.eich_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:27.995575+00:00
-- url     : https://prove2.me/submissions/4a7a330d-18b6-4947-b47f-6cf1fa8b1e2f

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eich_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicMeet_le_jointSpan

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
theorem _root_.solution (F F' : FlagD H r) {x v : V} {c : K} (hx : x ∈ II F F') {w : V}
    (hw : ∀ y ∈ V0 F F', H.B y w = 0) : eich H x v c w = w + H.B w v • x := by
  have hwx : H.B w x = 0 := B_swap0 H (hw x (isotropicMeet_le_jointSpan F F' hx))
  rw [eich_apply, hwx]
  simp
end Formalism.HermitianLatticeCounting.P
