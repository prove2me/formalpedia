-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.muDual_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:32.901023+00:00
-- url     : https://prove2.me/submissions/5fbb37e3-8141-4822-aa64-bc18bc1e1929

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieMu
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_mem_dualLat_iff
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cnorm_isom
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_norm_sq_realize
import Theorems.Thm_Formalism_HN_satR_mem_zl
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cQ_mul_XA
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cU_conj_mul
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_conjT_transpose_isom
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_dualFrame_inv
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_slope_eq_of_norm_eq
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_vecAt_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXA : ∀ v, IsUnit (A.X v).det) (hXE : ∀ v, IsUnit (XE v).det) :
    Formalism.HN.muDef (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat L) = A.muDual := by
  set ψ : Module.Dual K (Fin n → K) →ₗ[K] Module.Dual K A.V := Module.Dual.transpose e.symm.toLinearMap with hψ
  have hψx : ∀ f x, ψ f x = f (e.symm x) := fun f x => by simp [hψ, Module.Dual.transpose_apply]

  have hnA : ∀ v f, Formalism.HermitianLatticesTheory.normAt A.b.dualBasis (Formalism.HN.dualFrame A.X) v (ψ f) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) v f := by
    intro v f
    have hv := vecAt_map (Pi.basisFun K (Fin n)).dualBasis A.b.dualBasis v ψ f
    have hT : LinearMap.toMatrix (Pi.basisFun K (Fin n)).dualBasis A.b.dualBasis ψ =
        (LinearMap.toMatrix A.b (Pi.basisFun K (Fin n)) e.symm.toLinearMap)ᵀ := by
      rw [hψ, LinearMap.toMatrix_transpose]
    have hW : ((A.X v)ᵀ * (cQ A.b e v)ᵀ) = ((cU A.b A.X XE e v)ᴴ)ᵀ * (XE v)ᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, cQ_mul_XA A.b A.X XE e v hmet (hXA v) (hXE v)]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [hv, hT, dualFrame_inv A.X v (hXA v), dualFrame_inv XE v (hXE v), Matrix.mulVec_mulVec]
    have hQ : (LinearMap.toMatrix A.b (Pi.basisFun K (Fin n)) e.symm.toLinearMap)ᵀ.map v.embedding = (cQ A.b e v)ᵀ := rfl
    rw [hQ, hW, ← Matrix.mulVec_mulVec, cnorm_isom]
    rw [conjT_transpose_isom, cU_conj_mul A.b A.X XE e v hmet (hXE v), Matrix.transpose_one]
  have hn : ∀ f, ‖((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) f‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) f‖ := by
    intro f
    have h2 : ‖((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) f‖ ^ 2 =
        ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) f‖ ^ 2 := by
      rw [AddMonoidHom.comp_apply, Formalism.HN.PlaceOperatorNorms.norm_sq_realize, Formalism.HN.PlaceOperatorNorms.norm_sq_realize]
      simp only [LinearMap.toAddMonoidHom_coe, hnA]
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq (norm_nonneg _)]

  have hzl : Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)) (Formalism.HN.dualLat A.L) =
      Formalism.HN.zl ((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) (Formalism.HN.dualLat L) := by
    ext y
    rw [Formalism.HN.satR_mem_zl, Formalism.HN.satR_mem_zl]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨Module.Dual.transpose e.toLinearMap g, ?_, ?_⟩
      · rw [mem_dualLat_iff] at hg ⊢
        intro x hx
        simp only [Module.Dual.transpose_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
        exact hg (e x) (by rw [hlat]; exact ⟨x, hx, rfl⟩)
      · congr 1
        exact LinearMap.ext fun x => by simp [hψx, Module.Dual.transpose_apply]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨ψ f, ?_, rfl⟩
      rw [mem_dualLat_iff] at hf ⊢
      intro z hz
      rw [hlat] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      rw [hψx]
      simpa using hf x hx
  have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)) (Formalism.HN.dualLat A.L) =
      Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE)) (Formalism.HN.dualLat L) := by
    rw [← slope_eq_of_norm_eq _ _ hn (Formalism.HN.dualLat L)]
    unfold Formalism.HN.slope
    rw [hzl]
  unfold Formalism.BasicNotions.HLat.muDual Formalism.BasicNotions.HLat.dualB Formalism.BasicNotions.HLat.dualX Formalism.BasicNotions.HLat.dualL Formalism.HN.muDef
  rw [hs]
end Formalism.MainNotions.DIV.HookProducts.RBTie
