-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.level_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:33.341247+00:00
-- url     : https://prove2.me/submissions/7bbf51c4-bb6d-48c6-98f9-cba6f0f22893

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_notMem_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_notMem

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
theorem _root_.solution (F : FlagD H r) {x : V} {a b : Fin r} {al bl : K} (h : F.HasLevel x a al)
    (h' : F.HasLevel x b bl) : a = b ∧ al = bl := by
  obtain ⟨hal, hx⟩ := id h
  obtain ⟨hbl, hx'⟩ := id h'
  have hab : a = b := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (level_notMem F) h'
        ((Xa_mono F) (by have := Fin.lt_iff_val_lt_val.1 hlt; omega) ((level_mem F) h))
    · exact (level_notMem F) h
        ((Xa_mono F) (by have := Fin.lt_iff_val_lt_val.1 hlt; omega) ((level_mem F) h'))
  subst hab
  refine ⟨rfl, ?_⟩
  by_contra hne
  have h1 : (bl - al) • F.e a.castSucc ∈ F.Xa a.val := by
    have := Submodule.sub_mem _ hx hx'
    convert this using 1
    rw [sub_smul]
    abel
  exact (e_notMem_Xa F) a ((Submodule.smul_mem_iff _ (sub_ne_zero.2 (Ne.symm hne))).1 h1)
end Formalism.HermitianLatticeCounting.P
