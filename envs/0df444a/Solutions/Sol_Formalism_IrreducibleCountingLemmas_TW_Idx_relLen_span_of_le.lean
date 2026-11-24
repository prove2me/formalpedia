-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_span_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:26.506494+00:00
-- url     : https://prove2.me/submissions/f7d6cd0b-b891-465f-95d8-a007276608e0

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_length_quot_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {d : ℕ} (b : Basis (Fin d) K V) (w : Fin d → V)
    (hw : Submodule.span O (Set.range w) ≤ Submodule.span O (Set.range b))
    (hdet : b.det w ≠ 0) :
    ∃ D : O, algebraMap O K D = b.det w ∧
      relLen (Submodule.span O (Set.range b)) (Submodule.span O (Set.range w)) = Ring.ord O D := by
  let bO := b.restrictScalars O
  let w' : Fin d → Submodule.span O (Set.range b) :=
    fun i => ⟨w i, hw (Submodule.subset_span ⟨i, rfl⟩)⟩
  let f : Submodule.span O (Set.range b) →ₗ[O] Submodule.span O (Set.range b) := bO.constr O w'
  have hD : algebraMap O K (LinearMap.det f) = b.det w := by
    rw [← LinearMap.det_toMatrix bO, RingHom.map_det, Basis.det_apply]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, f, w', bO]
  have hne : LinearMap.det f ≠ 0 := by
    intro h; rw [h, map_zero] at hD; exact hdet hD.symm
  have hinj : Function.Injective f := by
    intro x y hxy
    have hM : (LinearMap.toMatrix bO bO f).det ≠ 0 := by rwa [LinearMap.det_toMatrix]
    have := Matrix.mulVec_injective_of_det_ne_zero hM (a₁ := bO.repr x) (a₂ := bO.repr y)
      (by rw [LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_mulVec_repr, hxy])
    exact bO.repr.injective (DFunLike.coe_injective this)
  have hrange : (Submodule.span O (Set.range w)).comap (Submodule.span O (Set.range b)).subtype
      = LinearMap.range f := by
    rw [Basis.constr_range]
    apply Submodule.map_injective_of_injective (Submodule.span O (Set.range b)).injective_subtype
    rw [Submodule.map_comap_subtype, Submodule.map_span, ← Set.range_comp, inf_eq_right.2 hw]
    rfl
  refine ⟨_, hD, ?_⟩
  unfold relLen
  rw [hrange]
  exact length_quot_range bO f hinj
end Formalism.IrreducibleCountingLemmas.TW.Idx
