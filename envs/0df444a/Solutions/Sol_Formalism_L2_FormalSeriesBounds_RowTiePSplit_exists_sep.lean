-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:46.852389+00:00
-- url     : https://prove2.me/submissions/96f9fb33-f4b6-4b6e-95a8-ad696cc111a5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_aff_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.FormalSeriesBounds.RowTiePSplit
theorem _root_.solution {O : Type} [CommRing O] {ι : Type} [Fintype ι] (em : ι → (O →+* K))
    (hem : Function.Injective em) : ∃ x0 : O, ∀ c c', c ≠ c' → em c x0 ≠ em c' x0 := by
  classical
  have key : ∀ F : Finset (ι × ι), (∀ q ∈ F, q.1 ≠ q.2) → ∃ x0 : O, ∀ q ∈ F, em q.1 x0 ≠ em q.2 x0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert p F _ ih =>
      intro hF
      obtain ⟨x, hx⟩ := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
      obtain ⟨z, hz⟩ : ∃ z, em p.1 z ≠ em p.2 z := by
        by_contra h
        push Not at h
        exact hF p (Finset.mem_insert_self p F) (hem (RingHom.ext h))
      have hfin : (⋃ q ∈ ((↑(insert p F) : Set (ι × ι))),
          {t : ℕ | (em q.1 x - em q.2 x) + (t : K) * (em q.1 z - em q.2 z) = 0}).Finite := by
        refine Set.Finite.biUnion (Finset.finite_toSet _) fun q hq => (aff_sub _ _ ?_).finite
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hq) with rfl | hq'
        · exact Or.inr (sub_ne_zero.2 hz)
        · exact Or.inl (sub_ne_zero.2 (hx q hq'))
      obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
      refine ⟨x + (t : O) * z, fun q hq h => ht (Set.mem_biUnion (Finset.mem_coe.2 hq) ?_)⟩
      simp only [Set.mem_ofPred_eq]
      simp only [map_add, map_mul, map_natCast] at h
      linear_combination h
  obtain ⟨x0, hx0⟩ := key (Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2)
    (fun q hq => (Finset.mem_filter.1 hq).2)
  exact ⟨x0, fun c c' hcc' => hx0 (c, c') (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcc'⟩)⟩
end Formalism.L2.FormalSeriesBounds.RowTiePSplit
