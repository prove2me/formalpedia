-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Xa_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:14.569279+00:00
-- url     : https://prove2.me/submissions/1c785e66-e06a-4c23-8af4-5b258d8165cb

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
theorem _root_.solution (F : FlagD H r) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  apply Submodule.span_mono
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b, lt_of_lt_of_le hb h, rfl⟩
end Formalism.HermitianLatticeCounting.P
