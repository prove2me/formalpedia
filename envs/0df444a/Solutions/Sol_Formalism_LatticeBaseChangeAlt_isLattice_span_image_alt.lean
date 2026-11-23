-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.isLattice_span_image_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:32.920032+00:00
-- url     : https://prove2.me/submissions/c40d64dd-9cb8-4bd9-aacd-c5c28d39623e

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LinearIndependentOfIsBaseChange
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_span_image_span_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : IsLatticeSpanImage := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj M hM
  classical
  unfold Formalism.LatticeIndexTer.IsLat at hM ⊢
  have hsm : ∀ (o : O) (x : V), j (o • x) = (algebraMap O O' o) • j x := by
    intro o x
    rw [← algebraMap_smul K o x, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j x),
      ← algebraMap_smul K' (algebraMap O O' o) (j x), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨⟨S, hS⟩, hM2⟩ := hM
  let P : Submodule O' V₁ := Submodule.span O' (j '' (S : Set V))
  let Q : Submodule O V :=
    { carrier := {x | j x ∈ P}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ P
        rw [map_add]
        exact P.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ P
        rw [map_zero]
        exact P.zero_mem
      smul_mem' := fun c x hx => by
        show j (c • x) ∈ P
        rw [hsm]
        exact P.smul_mem _ hx }
  have hQ : Submodule.span O (S : Set V) ≤ Q :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩)
  have hNP : Submodule.span O' (j '' (M : Set V)) = P := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [← hS] at hm
      exact hQ hm
    · apply Submodule.span_mono
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, by rw [← hS]; exact Submodule.subset_span hx, rfl⟩
  refine ⟨⟨S.image j, ?_⟩, ?_⟩
  · rw [Finset.coe_image, hNP]
  · rw [Submodule.span_span_of_tower, ← span_image_span_alt (K' := K') j (M : Set V), hM2]
    rw [eq_top_iff, ← (hj.basis (Module.finBasis K V)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Module.finBasis K V i, Submodule.mem_top, ?_⟩
    first
    | simp [IsBaseChange.basis_apply]
    | simp
end Formalism.LatticeBaseChangeAlt
