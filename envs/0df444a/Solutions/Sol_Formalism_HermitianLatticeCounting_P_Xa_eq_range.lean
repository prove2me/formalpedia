-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Xa_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:27.704534+00:00
-- url     : https://prove2.me/submissions/95681896-7896-45c3-bd4d-6bc8ba6b8dc1

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
theorem _root_.solution (F : FlagD H r) {j : ℕ} (hj : j ≤ r) :
    F.Xa j = Submodule.span K
      (Set.range fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  congr 1
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.val, hb⟩, congrArg F.e (Fin.ext rfl)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, by have := a.isLt; omega⟩, a.isLt, congrArg F.e (Fin.ext rfl)⟩
end Formalism.HermitianLatticeCounting.P
