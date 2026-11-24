-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.inter_baseChange_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:07:44.370817+00:00
-- url     : https://prove2.me/submissions/4430ddca-bfc7-4761-9e29-bc14d4e780ca

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Lemmata_MiscLemmasO_Imports
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSmulMemOfMemSpan
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_exists_adapted_basis_alt

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
theorem _root_.solution : SpanImageInf := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj M V' hM
  obtain ⟨b, s, hMb, hs, hV'⟩ := exists_adapted_basis_alt O K V M V' hM
  let b' : Basis (Fin (finrank K V)) K' V₁ := hj.basis b
  have hb' : ∀ i, b' i = j (b i) := fun i => hj.basis_apply b i
  have hjO : ∀ (o : O) (v : V), j (o • v) = algebraMap O O' o • j v := by
    intro o v
    rw [← algebraMap_smul K o v, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j v),
      ← algebraMap_smul K' (algebraMap O O' o) (j v), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hjK : ∀ (k : K) (v : V), j (k • v) = algebraMap K K' k • j v := by
    intro k v
    rw [map_smul, algebraMap_smul]
  have hO : ∀ y ∈ Submodule.span O (Set.range b), j y ∈ Submodule.span O' (Set.range b') := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjO]; exact Submodule.smul_mem _ _ hy
  have hK : ∀ y ∈ Submodule.span K (b '' s), j y ∈ Submodule.span K' (b' '' s) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hi, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjK]; exact Submodule.smul_mem _ _ hy
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have h1 : x ∈ Submodule.span O' (Set.range b') := by
      refine (Submodule.span_le.mpr ?_) hx1
      rintro _ ⟨m, hm, rfl⟩
      exact hO m (hMb hm)
    have h2 : x ∈ Submodule.span K' (b' '' s) := by
      refine (Submodule.span_le.mpr ?_) hx2
      rintro _ ⟨m, hm, rfl⟩
      exact hK m (hV' hm)
    rw [b'.mem_span_iff_repr_mem O'] at h1
    rw [b'.mem_span_image] at h2
    rw [← b'.sum_repr x]
    refine Submodule.sum_mem _ ?_
    intro i _
    by_cases hi : i ∈ s
    · obtain ⟨c, hc⟩ := h1 i
      rw [← hc, algebraMap_smul, hb']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hs i hi, rfl⟩)
    · have : b'.repr x i = 0 := by
        by_contra h0
        exact hi (h2 (by simpa using h0))
      rw [this, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨m, hm1, rfl⟩, Submodule.subset_span ⟨m, hm2, rfl⟩⟩
end Formalism.LatticeBaseChangeAlt
