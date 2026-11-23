-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.RowCol.length_le_of_killed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:02.803982+00:00
-- url     : https://prove2.me/submissions/2d13fa3e-34aa-4f75-a857-1aa016a6be75

import Definitions.Def_Formalism_WachLatticeTwists_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.RowCol
open Module
namespace Formalism.RepresentationBoundsCohomology.RowCol
theorem _root_.solution {O : Type*} [CommRing O] (b : O) {X : Type*} [AddCommGroup X]
    [Module O X] {ι : Type*} [Fintype ι] (g : (ι → O) →ₗ[O] X) (hg : Function.Surjective g)
    (hb : ∀ x : X, b • x = 0) :
    Module.length O X ≤ (Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {b}) := by
  classical
  let gi : ι → (O →ₗ[O] X) := fun i =>
    LinearMap.toSpanSingleton O X (g (fun j => if i = j then 1 else 0))
  have hker : ∀ i, Ideal.span {b} ≤ LinearMap.ker (gi i) := by
    intro i
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_ker.mpr (hb _)
  let h : (ι → O ⧸ Ideal.span {b}) →ₗ[O] X :=
    ∑ i, (Submodule.liftQ (Ideal.span {b}) (gi i) (hker i)).comp (LinearMap.proj i)
  have hs : Function.Surjective h := by
    intro x
    obtain ⟨v, rfl⟩ := hg x
    refine ⟨fun i => Submodule.Quotient.mk (v i), ?_⟩
    simp only [h, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.liftQ_apply, gi, LinearMap.toSpanSingleton_apply]
    conv_rhs => rw [pi_eq_sum_univ v]
    rw [map_sum]
    simp only [map_smul]
  calc Module.length O X ≤ Module.length O (ι → O ⧸ Ideal.span {b}) :=
        Module.length_le_of_surjective h hs
    _ = _ := by rw [Module.length_pi, ENat.card_eq_coe_fintype_card]
end Formalism.RepresentationBoundsCohomology.RowCol
