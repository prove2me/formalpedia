-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LatticeIndexBis.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:16.74553+00:00
-- url     : https://prove2.me/submissions/8ca06398-5f90-4425-8f37-f9715c208941

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_idx_map_inj
import Theorems.Thm_Formalism_LatticeIndexTer_idxDet


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
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis
variable {O K V ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
namespace Formalism.LatticeBaseChangeAlt.LatticeIndexBis
theorem _root_.solution [Fintype ι] [DecidableEq ι] (a b : ι → V) (ha : LinearIndependent K a)
    (hb : LinearIndependent K b)
    (hab : Submodule.span K (Set.range a) = Submodule.span K (Set.range b))
    (P : Matrix ι ι K) (hP : ∀ i, a i = ∑ k, P k i • b k) :
    P.det ≠ 0 ∧ ∀ x y : O, x ≠ 0 → y ≠ 0 → algebraMap O K x = P.det * algebraMap O K y →
      Formalism.LatticeIndexTer.idx O V (Submodule.span O (Set.range b)) (Submodule.span O (Set.range a)) =
        ((IsDiscreteValuationRing.addVal O x).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O y).toNat : ℤ) := by
  let bX := Basis.span ha
  let bY := Basis.span hb
  let f : Submodule.span K (Set.range a) ≃ₗ[K] Submodule.span K (Set.range b) :=
    LinearEquiv.ofEq _ _ hab
  have hbX : ∀ i, ((bX i : Submodule.span K (Set.range a)) : V) = a i := fun i => by
    simp [bX, Basis.span_apply]
  have hbY : ∀ i, ((bY i : Submodule.span K (Set.range b)) : V) = b i := fun i => by
    simp [bY, Basis.span_apply]
  have hM : LinearMap.toMatrix bX bY (f : _ →ₗ[K] _) = P := by
    ext k i
    rw [LinearMap.toMatrix_apply]
    have : (f : _ →ₗ[K] _) (bX i) = ∑ k, P k i • bY k := by
      apply Subtype.ext
      simp [f, hbX, hbY, hP i]
    rw [this, Basis.repr_sum_self]
  refine ⟨?_, ?_⟩
  · rw [← hM]
    exact (LinearEquiv.isUnit_det f bX bY).ne_zero
  · intro x y hx hy hxy
    have h := Formalism.LatticeIndexTer.idxDet O K _ _ ι bX bY f x y hx hy (by rw [hM]; exact hxy)
    let s : Submodule.span K (Set.range b) →ₗ[O] V :=
      (Submodule.span K (Set.range b)).subtype.restrictScalars O
    have hs : Function.Injective s := Subtype.val_injective
    rw [← idx_map_inj s hs] at h
    rw [← h]
    congr 1
    · rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      ext i
      exact (hbY i).symm
    · rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
      congr 2
      ext i
      exact (hbX i).symm
end Formalism.LatticeBaseChangeAlt.LatticeIndexBis
