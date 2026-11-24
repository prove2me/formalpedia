-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.exists_unitary_one_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:02:19.336258+00:00
-- url     : https://prove2.me/submissions/37d9bd47-a3c3-48d8-8df9-7529ee281101

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ExistsUnitaryOneDetEq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution (σ : E →ₐ[F] E) (G : GL m 𝒜) (hG : G ∈ UPts σ (1 : Matrix m m E) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ x : GL (Fin 1) 𝒜, x ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det x = Matrix.GeneralLinearGroup.det G := by
  have hmap1 : ∀ {p : Type} [Fintype p] [DecidableEq p], (1 : Matrix p p E).map ιA = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hG' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (G : Matrix m m 𝒜) * (1 : Matrix m m E).map ιA *
      (G : Matrix m m 𝒜) = (1 : Matrix m m E).map ιA := hG
  rw [hmap1, Matrix.mul_one] at hG'
  set u : 𝒜ˣ := Matrix.GeneralLinearGroup.det G with hu
  have hud : (u : 𝒜) = Matrix.det (G : Matrix m m 𝒜) := Matrix.GeneralLinearGroup.val_det_apply G
  have hd : sigR σ (FiniteAdeleRing (𝓞 F) F) (u : 𝒜) * (u : 𝒜) = 1 := by
    have h := congrArg Matrix.det hG'
    rw [Matrix.det_mul, Matrix.det_one] at h
    unfold Formalism.UG.cT at h
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
    rw [hud]
    exact h
  let x : GL (Fin 1) 𝒜 :=
    ⟨Matrix.diagonal (fun _ => (u : 𝒜)), Matrix.diagonal (fun _ => ((u⁻¹ : 𝒜ˣ) : 𝒜)),
      by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
  refine ⟨x, ?_, ?_⟩
  · show cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Matrix.diagonal (fun _ : Fin 1 => (u : 𝒜))) *
        (1 : Matrix (Fin 1) (Fin 1) E).map ιA * Matrix.diagonal (fun _ : Fin 1 => (u : 𝒜)) =
        (1 : Matrix (Fin 1) (Fin 1) E).map ιA
    rw [hmap1, Matrix.mul_one]
    unfold Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hd
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show Matrix.det (Matrix.diagonal (fun _ : Fin 1 => (u : 𝒜))) = (u : 𝒜)
    rw [Matrix.det_diagonal]
    simp
end Formalism.L2.GlobalTheoryTheory.Comp
