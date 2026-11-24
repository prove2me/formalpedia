-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.381247+00:00
-- url     : https://prove2.me/submissions/4949434c-1957-43c9-bb77-86aeb562e3d9

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_dualBasis
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_zmap_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_ri_zmap
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_mem_zmap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (A : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι A)] [IsZLattice ℝ (zmap ι A)]
    (D : ℕ) (hD0 : 0 < D) (hD : ∀ x ∈ A, D • x ∈ genusCovol_tdual h A) :
    (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 ∧
    (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup ≠ 0 ∧
    ZLattice.covolume (zmap ι A) ^ 2 *
        ((A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ((A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup : ℝ) := by
  classical
  obtain ⟨bv, hE2, hprod⟩ := genusCovol_dualBasis h N ι hι A
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have h1 := hpos x hne
    have h2 := hι x x
    rw [hx, inner_zero_left] at h2
    have : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = 0 := h2.symm
    have : Algebra.trace ℚ K (h x x) = 0 := by exact_mod_cast this
    exact lt_irrefl _ (this ▸ h1)
  set Λ := zmap ι A with hΛ
  set NE := zmap ι (A ⊓ genusCovol_tdual h A) with hNE
  have hNΛ : NE ≤ Λ := genusCovol_zmap_mono N ι inf_le_left
  have hNT : NE ≤ Submodule.span ℤ (Set.range bv) := hE2 ▸ genusCovol_zmap_mono N ι inf_le_right
  haveI : DiscreteTopology NE :=
    DiscreteTopology.of_subset (s := (Λ : Set (EuclideanSpace ℝ (Fin N)))) inferInstance hNΛ
  haveI : IsZLattice ℝ NE := by
    refine ⟨?_⟩
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ), Submodule.span_le]
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (genusCovolBound_mem_zmap N ι A v).mp hv
    have hDx : ι (D • x) ∈ NE :=
      (genusCovolBound_mem_zmap N ι _ _).mpr ⟨D • x, ⟨A.nsmul_mem hx D, hD x hx⟩, rfl⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at hDx
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD0.ne'
    have : ι x = (D : ℝ)⁻¹ • ((D : ℝ) • ι x) := by rw [smul_smul, inv_mul_cancel₀ hD', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hDx)
  have e1 := ZLattice.covolume_div_covolume_eq_relIndex' NE Λ hNΛ
  have e2 := ZLattice.covolume_div_covolume_eq_relIndex' NE _ hNT
  have hri1 : NE.toAddSubgroup.relIndex Λ.toAddSubgroup =
      (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup := by
    rw [hNE, hΛ, genusCovol_ri_zmap N ι hinj]
  rw [hri1] at e1
  have hri2 : NE.toAddSubgroup.relIndex (Submodule.span ℤ (Set.range bv)).toAddSubgroup =
      (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup := by
    rw [← hE2, hNE, genusCovol_ri_zmap N ι hinj]
  rw [hri2] at e2
  have hc := ZLattice.covolume_pos Λ
  have hc' := ZLattice.covolume_pos (Submodule.span ℤ (Set.range bv))
  have hn := ZLattice.covolume_pos NE
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    rw [h0, Nat.cast_zero] at e1
    exact (div_pos hn hc).ne' e1
  · intro h0
    rw [h0, Nat.cast_zero] at e2
    exact (div_pos hn hc').ne' e2
  · rw [← e1, ← e2]
    have hc'eq := eq_inv_of_mul_eq_one_right hprod
    rw [hc'eq, div_inv_eq_mul, ← hΛ]
    field_simp
end Formalism.HermitianLatticesTheory
