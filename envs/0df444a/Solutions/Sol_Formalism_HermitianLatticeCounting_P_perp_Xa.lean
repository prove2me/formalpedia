-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.perp_Xa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:35.109915+00:00
-- url     : https://prove2.me/submissions/4acb84e3-8334-488e-a5ee-b59e6ac8ac5c

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_span

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
theorem _root_.solution (F : FlagD H r) {a : ℕ} {v : V}
    (h : ∀ b : Fin r, b.val < a → H.B (F.e b.castSucc) v = 0) : ∀ u ∈ F.Xa a, H.B u v = 0 := by
  intro u hu
  refine perp_span H (S := (fun b : Fin r => F.e b.castSucc) '' {b | b.val < a}) ?_ u hu
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb
end Formalism.HermitianLatticeCounting.P
