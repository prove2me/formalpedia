-- Prove2me | solution 1 for Ehrhart.GenuineJetAdaptedBasisCounting.span_adaptedIndices_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/843d407b-4b5c-4665-941b-6b09ee826e69

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.GenuineJetAdaptedBasisCounting
open Set Module
open scoped BigOperators InnerProductSpace
namespace Ehrhart.GenuineJetAdaptedBasisCounting
theorem _root_.solution {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : OrthonormalBasis ι ℂ V) (S : Submodule ℂ V)
    (hb : ∀ i, b i ∈ S ∨ b i ∈ Sᗮ) :
    Submodule.span ℂ
      (Set.range (fun i : adaptedIndices b S => b (i : ι))) = S := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : (i : ι) ∈
        Finset.univ.filter (fun q => b q ∈ S) := i.property
    exact (Finset.mem_filter.mp hi).2
  · intro x hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : b i ∈ S
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨⟨i, ?_⟩, rfl⟩
      simpa [adaptedIndices] using hi
    · have horth : b i ∈ Sᗮ := (hb i).resolve_left hi
      have hcoeff : b.repr x i = 0 := by
        rw [b.repr_apply_apply]
        exact (Submodule.mem_orthogonal' S (b i)).mp horth x hx
      simp [hcoeff]
end Ehrhart.GenuineJetAdaptedBasisCounting
