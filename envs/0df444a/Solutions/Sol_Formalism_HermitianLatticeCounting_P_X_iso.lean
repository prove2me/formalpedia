-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.X_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:24:59.194687+00:00
-- url     : https://prove2.me/submissions/0db47e20-da43-48d6-9d97-0e6ccfa4de4c

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X

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
theorem _root_.solution (F : FlagD H r) {u v : V} (hu : u ∈ F.X) (hv : v ∈ F.X) : H.B u v = 0 := by
  have h1 : ∀ b : Fin r, ∀ w ∈ F.X, H.B w (F.e b.castSucc) = 0 :=
    fun b => (perp_X F) (fun b' => F.iso b' b)
  exact (perp_X F) (fun b => B_swap0 H (h1 b v hv)) u hu
end Formalism.HermitianLatticeCounting.P
