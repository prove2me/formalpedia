-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Dl_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:16.026941+00:00
-- url     : https://prove2.me/submissions/c493d3da-76fe-46c1-ad2f-ccc7e65dc6d9

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_eq

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
theorem _root_.solution (F F' : FlagD H r) (l : ℕ) (hl : l ≤ r + 1) : Dl F' F l hl = star (Dl F F' l hl) := by
  rw [Dl_eq, Dl_eq, ← Matrix.det_conjTranspose]
  congr 1
  ext a b
  simp [Matrix.conjTranspose_apply, H.herm]
end Formalism.HermitianLatticeCounting.P
