-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.level_lt_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:32.159212+00:00
-- url     : https://prove2.me/submissions/ffe8035a-b64b-466e-a572-7b222480c066

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_notMem

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
theorem _root_.solution (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) {n : ℕ}
    (hx : x ∈ F.Xa n) : a.val < n := by
  by_contra hlt
  push_neg at hlt
  exact (level_notMem F) h ((Xa_mono F) hlt hx)
end Formalism.HermitianLatticeCounting.P
