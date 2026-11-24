-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.len_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:51:15.545796+00:00
-- url     : https://prove2.me/submissions/006d9128-2fb4-4c73-bc77-6adf418b44be

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_length_quot_range
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_repr_of_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
variable {O K Y ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup Y] [Module K Y] [Module O Y]
  [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution (b : Basis ι K Y) (w : ι → Y) (hw : ∀ j, w j ∈ Submodule.span O (Set.range b))
    (hdet : (b.toMatrix w).det ≠ 0) :
    ∃ e : O, algebraMap O K e = (b.toMatrix w).det ∧
      Module.length O (Submodule.span O (Set.range b) ⧸
        (Submodule.span O (Set.range w)).comap (Submodule.span O (Set.range b)).subtype) =
        IsDiscreteValuationRing.addVal O e := by
  set L := Submodule.span O (Set.range b) with hLdef
  have li : LinearIndependent O b :=
    LinearIndependent.restrict_scalars' (R := O) (K := K) b.linearIndependent
  let bO : Basis ι O L := Basis.span li
  have hrepr : ∀ (z : L) i, b.repr z i = algebraMap O K (bO.repr z i) :=
    fun z i => repr_of_mem_span b li z i
  have : Module.Free O L := Module.Free.of_basis bO
  have : Module.Finite O L := Module.Finite.of_basis bO
  let φ : L →ₗ[O] L := bO.constr O (fun j => ⟨w j, hw j⟩)
  have hφ : ∀ z : L, (φ z : Y) = ∑ j, bO.equivFun z j • w j := by
    intro z
    simp only [φ, Basis.constr_apply_fintype, Submodule.coe_sum, Submodule.coe_smul]
  have hwK : LinearIndependent K w :=
    ((b.is_basis_iff_det).2 (by rw [Basis.det_apply]; exact isUnit_iff_ne_zero.2 hdet)).1
  have hwO : LinearIndependent O w :=
    LinearIndependent.restrict_scalars' (R := O) (K := K) hwK
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h0 : ∑ j, bO.equivFun z j • w j = 0 := by rw [← hφ, hz]; rfl
    have h1 := Fintype.linearIndependent_iff.1 hwO _ h0
    apply bO.equivFun.injective
    funext j
    simp [h1 j]
  have hrange : LinearMap.range φ = (Submodule.span O (Set.range w)).comap L.subtype := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      show (φ z : Y) ∈ Submodule.span O (Set.range w)
      rw [hφ]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro hy
      have hy' : (y : Y) ∈ Submodule.span O (Set.range w) := hy
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hy'
      refine ⟨bO.equivFun.symm g, Subtype.ext ?_⟩
      rw [hφ, LinearEquiv.apply_symm_apply, hg]
  have hH : ∀ i j, algebraMap O K (LinearMap.toMatrix bO bO φ i j) = b.toMatrix w i j := by
    intro i j
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    simp only [φ, Basis.constr_basis]
    exact (hrepr ⟨w j, hw j⟩ i).symm
  refine ⟨LinearMap.det φ, ?_, ?_⟩
  · rw [← LinearMap.det_toMatrix bO, RingHom.map_det]
    congr 1
    ext i j
    exact hH i j
  · rw [← hrange, length_quot_range φ hinj]
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
