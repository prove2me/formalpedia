-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.X_eq_of_levels
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:40.097795+00:00
-- url     : https://prove2.me/submissions/278589e5-0533-411a-b797-daa732061692

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_succ

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
theorem _root_.solution (F : FlagD H r) (j : ℕ) (I : Submodule K V) (hI : I ≤ F.X)
    (h : ∀ a : Fin r, j ≤ a.val → ∃ x ∈ I, ∃ al : K, F.HasLevel x a al) : F.X = F.Xa j ⊔ I := by
  apply le_antisymm
  · have key : ∀ n, n ≤ r → F.Xa n ≤ F.Xa j ⊔ I := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [(Xa_zero F)]
        exact bot_le
      | succ n ih =>
        intro hn
        have hnr : n < r := by omega
        have hsb : F.Xa (n + 1) = F.Xa n ⊔ K ∙ F.e (⟨n, hnr⟩ : Fin r).castSucc :=
          (Xa_succ F) ⟨n, hnr⟩
        rw [hsb]
        refine sup_le (ih (by omega)) ?_
        rw [Submodule.span_singleton_le_iff_mem]
        by_cases hjn : j ≤ n
        · obtain ⟨x, hxI, al, hal⟩ := h ⟨n, hnr⟩ hjn
          obtain ⟨hal0, hxa⟩ := id hal
          have h1 : x - al • F.e (⟨n, hnr⟩ : Fin r).castSucc ∈ F.Xa j ⊔ I := ih (by omega) hxa
          have h2 : x ∈ F.Xa j ⊔ I := Submodule.mem_sup_right hxI
          have h3 : al • F.e (⟨n, hnr⟩ : Fin r).castSucc ∈ F.Xa j ⊔ I := by
            simpa using Submodule.sub_mem _ h2 h1
          exact (Submodule.smul_mem_iff _ hal0).1 h3
        · exact Submodule.mem_sup_left ((e_mem_Xa F) _ (show n < j by omega))
    exact key r le_rfl
  · exact sup_le ((Xa_le_X F) j) hI
end Formalism.HermitianLatticeCounting.P
