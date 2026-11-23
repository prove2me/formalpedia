-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:14.7348+00:00
-- url     : https://prove2.me/submissions/24a4dad9-1f6d-4223-99ca-041e76436d42

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
theorem _root_.solution {A : Type} [CommRing A] (τ : A →+* A) (J' : Matrix m m A) (Q : Matrix m n A)
    (x y : n → A) : hform τ J' (Q *ᵥ x) (Q *ᵥ y) = hform τ (cT τ Q * J' * Q) x y := by
  have H : ∀ {p : Type} [Fintype p] (M : Matrix p p A) (a b : p → A),
      ∑ i, ∑ j, a i * M i j * b j = (a ᵥ* M) ⬝ᵥ b := by
    intro p _ M a b
    simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  unfold Formalism.UG.hform Formalism.UG.cT
  rw [show (∑ i, ∑ j, τ ((Q *ᵥ x) i) * J' i j * (Q *ᵥ y) j)
      = ((fun i => τ ((Q *ᵥ x) i)) ᵥ* J') ⬝ᵥ (Q *ᵥ y) from H _ _ _,
    show (∑ i, ∑ j, τ (x i) * ((Q.map τ)ᵀ * J' * Q) i j * y j)
      = ((fun i => τ (x i)) ᵥ* ((Q.map τ)ᵀ * J' * Q)) ⬝ᵥ y from H _ _ _]
  have hx : (fun i => τ ((Q *ᵥ x) i)) = (fun i => τ (x i)) ᵥ* (Q.map τ)ᵀ := by
    rw [Matrix.vecMul_transpose]
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hx, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]
end Formalism.L2.GlobalTheoryTheory.Comp
