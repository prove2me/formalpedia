-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.level_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:06.848648+00:00
-- url     : https://prove2.me/submissions/7646cf74-630b-47a8-b2f8-cf10b582427c

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa

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
theorem _root_.solution (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) :
    x ∈ F.Xa (a.val + 1) := by
  obtain ⟨hal, hx⟩ := h
  have h1 : x - al • F.e a.castSucc ∈ F.Xa (a.val + 1) := (Xa_mono F) (Nat.le_succ _) hx
  have h2 : F.e a.castSucc ∈ F.Xa (a.val + 1) := (e_mem_Xa F) a (Nat.lt_succ_self _)
  simpa using Submodule.add_mem _ h1 (Submodule.smul_mem _ al h2)
end Formalism.HermitianLatticeCounting.P
