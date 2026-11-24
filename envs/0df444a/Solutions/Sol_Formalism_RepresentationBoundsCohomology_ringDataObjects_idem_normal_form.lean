-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.idem_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:34.125737+00:00
-- url     : https://prove2.me/submissions/80def434-a032-4935-ab98-621a060ec5f2

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_free_of_isCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution [IsLocalRing O] (e : Matrix r r O) (he : IsIdempotentElem e) :
    ∃ (P Q : Matrix r r O) (d : r → O), (∀ j, d j = 0 ∨ d j = 1) ∧ P * Q = 1 ∧ Q * P = 1 ∧
      e = P * Matrix.diagonal d * Q := by
  classical
  let E : (r → O) →ₗ[O] (r → O) := Matrix.toLin' e
  have hE : IsIdempotentElem E := by
    have h : E * E = E := by rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he.eq]
    exact h
  have hC : IsCompl (LinearMap.range E) (LinearMap.ker E) := LinearMap.IsIdempotentElem.isCompl hE
  obtain ⟨_, _⟩ := free_of_isCompl _ _ hC
  obtain ⟨_, _⟩ := free_of_isCompl _ _ hC.symm
  let bR := Module.Free.chooseBasis O (LinearMap.range E)
  let bK := Module.Free.chooseBasis O (LinearMap.ker E)
  let B := (bR.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hC)
  let σ := B.indexEquiv (Pi.basisFun O r)
  let B' := B.reindex σ
  have key : ∀ j, E (B' j) = (if (σ.symm j).isLeft then 1 else 0 : O) • B' j := by
    intro j
    simp only [B', Module.Basis.reindex_apply]
    rcases σ.symm j with a | b
    · have hm : (B (Sum.inl a)) ∈ LinearMap.range E := by
        simp [B, Module.Basis.prod_apply]
      simpa using ((LinearMap.IsIdempotentElem.mem_range_iff hE).mp hm)
    · have hm : (B (Sum.inr b)) ∈ LinearMap.ker E := by
        simp [B, Module.Basis.prod_apply]
      simpa using hm
  refine ⟨(Pi.basisFun O r).toMatrix B', B'.toMatrix (Pi.basisFun O r),
    fun j => if (σ.symm j).isLeft then 1 else 0, fun j => by dsimp only; split_ifs <;> simp,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  have hEP : e * (Pi.basisFun O r).toMatrix B' = (Pi.basisFun O r).toMatrix B' *
      Matrix.diagonal (fun j => if (σ.symm j).isLeft then 1 else 0) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (key j) i
    simp only [E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul] at this
    simp only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this, mul_comm]
  calc e = e * ((Pi.basisFun O r).toMatrix B' * B'.toMatrix (Pi.basisFun O r)) := by
        rw [Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hEP]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
