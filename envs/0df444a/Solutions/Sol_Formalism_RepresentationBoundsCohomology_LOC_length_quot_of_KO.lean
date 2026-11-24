-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.length_quot_of_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:57.412473+00:00
-- url     : https://prove2.me/submissions/1ffd3042-1c75-41a8-a623-16e2e4bce5d0

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_length_quot_le_of_surj
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_length_coker_eq_ker
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_pi_torsion
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_span_killed
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_span
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_RowCol_length_le_of_killed
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_submoduleLengthBound_statement


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {Q N : Type u} [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    [AddCommGroup N] [Module O N] {d : ℕ} (ι : N →ₗ[O] (Fin d → KO O)) (hι : Function.Injective ι)
    (δ : N →ₗ[O] Q) (hδ : Function.Surjective δ) (ℓ e : ℕ) :
    Module.length O (Q ⧸ mulSub ((ℓ : O) ^ e) Q) ≤ (d : ℕ∞) * ((e : ℕ∞) * eO O ℓ) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule O Q).FG)
  let f : Q → N := Function.surjInv hδ
  have hf : ∀ x, δ (f x) = x := Function.surjInv_eq hδ
  let t : Finset N := s.image f
  let N₂ : Submodule O N := Submodule.span O (t : Set N)
  have ht : ∀ x : N, ∃ c : O, c ≠ 0 ∧ c • x = 0 := by
    intro x
    obtain ⟨c, hc, h⟩ := pi_torsion (ι x)
    refine ⟨c, hc, hι ?_⟩
    rw [map_smul, h, map_zero]
  obtain ⟨c, hc, hkill⟩ := span_killed ht t
  have hfg : N₂.FG := ⟨t, rfl⟩
  have : Module.Finite O N₂ := Module.Finite.iff_fg.2 hfg

  have hfin : Module.length O N₂ ≠ ⊤ := by
    obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' O N₂
    have h1 := Formalism.RepresentationBoundsCohomology.RowCol.length_le_of_killed c g hg (by
      intro x
      exact Subtype.ext (hkill x x.2))
    rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Fintype.card_fin] at h1
    have h2 : IsDiscreteValuationRing.addVal O c ≠ ⊤ :=
      fun h' => hc (IsDiscreteValuationRing.addVal_eq_top_iff.1 h')
    intro h
    rw [h, top_le_iff] at h1
    lift IsDiscreteValuationRing.addVal O c to ℕ using h2 with v
    exact ENat.natCast_ne_top (k * v) (by exact_mod_cast h1)

  let δ₂ : N₂ →ₗ[O] Q := δ ∘ₗ N₂.subtype
  have hδ₂ : Function.Surjective δ₂ := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype, eq_top_iff, ← hs,
      Submodule.span_le]
    intro x hx
    exact ⟨f x, Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)), hf x⟩
  refine (length_quot_le_of_surj δ₂ hδ₂).trans ?_
  rw [length_coker_eq_ker _ hfin]

  let κ := LinearMap.ker (LinearMap.lsmul O N₂ ((ℓ : O) ^ e))
  let j : κ →ₗ[O] (Fin d → KO O) := ι ∘ₗ N₂.subtype ∘ₗ κ.subtype
  have hj : Function.Injective j :=
    hι.comp (N₂.injective_subtype.comp κ.injective_subtype)
  have h0 := Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O (Fin d) (LinearMap.range j) ℓ e (by
    rintro _ ⟨x, rfl⟩
    rw [← map_smul]
    have : ((ℓ : O) ^ e) • x = 0 := Subtype.ext x.2
    rw [this, map_zero])
  rw [Fintype.card_fin] at h0
  exact (Module.length_le_of_injective j.rangeRestrict (by
    intro x y hxy
    exact hj (congrArg Subtype.val hxy))).trans h0
end Formalism.RepresentationBoundsCohomology.LOC
