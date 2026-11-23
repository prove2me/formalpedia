-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.perp_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:18.575794+00:00
-- url     : https://prove2.me/submissions/3d39c3cf-c845-4325-8f2b-aa9cfe4325a6

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
theorem _root_.solution (H : HermSpace K V) {S : Set V} {v : V} (h : ∀ s ∈ S, H.B s v = 0) :
    ∀ u ∈ Submodule.span K S, H.B u v = 0 := by
  have hle : Submodule.span K S ≤ LinearMap.ker (H.B.flip v) := by
    rw [Submodule.span_le]
    intro s hs
    simp [h s hs]
  intro u hu
  simpa using hle hu
end Formalism.HermitianLatticeCounting.P
