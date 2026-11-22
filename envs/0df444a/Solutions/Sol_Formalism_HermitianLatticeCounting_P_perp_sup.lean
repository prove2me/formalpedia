-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.perp_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:21.597226+00:00
-- url     : https://prove2.me/submissions/7d28b8f0-ecba-41c4-ac09-c178ea906042

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
theorem _root_.solution (H : HermSpace K V) {S T : Submodule K V} {v : V} (h : ∀ s ∈ S, H.B s v = 0)
    (h' : ∀ s ∈ T, H.B s v = 0) : ∀ u ∈ S ⊔ T, H.B u v = 0 := by
  have hle : S ⊔ T ≤ LinearMap.ker (H.B.flip v) :=
    sup_le (fun s hs => by simp [h s hs]) (fun s hs => by simp [h' s hs])
  intro u hu
  simpa using hle hu
end Formalism.HermitianLatticeCounting.P
