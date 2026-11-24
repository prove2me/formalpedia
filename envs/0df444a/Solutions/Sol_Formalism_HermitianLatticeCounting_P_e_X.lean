-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.e_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:43.36991+00:00
-- url     : https://prove2.me/submissions/f9524b6b-bb69-4f55-b7a3-8f315f6fd22b

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X

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
theorem _root_.solution (F : FlagD H r) (i : Fin (r + 1)) {u : V} (hu : u ∈ F.X) : H.B (F.e i) u = 0 := by
  induction i using Fin.lastCases with
  | last => exact (z_X F) hu
  | cast b => exact B_swap0 H ((perp_X F) (fun b' => F.iso b' b) u hu)
end Formalism.HermitianLatticeCounting.P
