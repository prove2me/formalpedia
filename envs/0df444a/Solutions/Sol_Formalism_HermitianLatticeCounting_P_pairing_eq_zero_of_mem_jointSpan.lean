-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.pairing_eq_zero_of_mem_jointSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:35.006179+00:00
-- url     : https://prove2.me/submissions/f51613ec-d792-4f1b-a191-c16e1d37208b

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_span
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_sup

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
theorem _root_.solution (F F' : FlagD H r) {v : V} (h1 : ∀ u ∈ F.X, H.B u v = 0) (h2 : ∀ u ∈ F'.X, H.B u v = 0)
    (h3 : H.B F.z v = 0) (h4 : H.B F'.z v = 0) : ∀ u ∈ V0 F F', H.B u v = 0 := by
  intro u hu
  unfold Formalism.HermitianLatticeCounting.S6.V0 at hu
  refine perp_sup H (S := F.X ⊔ F'.X)
    (T := Submodule.span K {F.z, F'.z}) (perp_sup H h1 h2) ?_ u hu
  apply perp_span H
  intro s hs
  rcases hs with rfl | hs
  · exact h3
  · rw [Set.mem_singleton_iff.1 hs]
    exact h4
end Formalism.HermitianLatticeCounting.P
