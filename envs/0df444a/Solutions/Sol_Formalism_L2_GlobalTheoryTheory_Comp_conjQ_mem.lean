-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.conjQ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:15.834314+00:00
-- url     : https://prove2.me/submissions/bb1ff4d5-665d-466c-86c7-faf613eb2e29

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ExistsUnitaryOneDetEq
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_cT_map
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
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) (hQ : cT (σ : E →+* E) Q * (1 : Matrix m m E) * Q = J) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    conjQ Q Q' h1 h2 g ∈ UPts σ (1 : Matrix m m E) (FiniteAdeleRing (𝓞 F) F) := by
  have hcTA : ∀ {p q r : Type} [Fintype q] (M : Matrix p q (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
      (N : Matrix q r (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (M * N) =
        cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) N * cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) M := by
    intro p q r _ M N
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hcTE : ∀ {p q r : Type} [Fintype q] (M : Matrix p q E) (N : Matrix q r E),
      cT (σ : E →+* E) (M * N) = cT (σ : E →+* E) N * cT (σ : E →+* E) M := by
    intro p q r _ M N
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hcT1 : cT (σ : E →+* E) (1 : Matrix m m E) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hmap1 : (1 : Matrix m m E).map ιA = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hA : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA) * Q.map ιA = J.map ιA := by
    rw [cT_map, ← Matrix.map_mul, ← hQ, Matrix.mul_one]
  have hE : cT (σ : E →+* E) Q' * J * Q' = 1 := by
    rw [← hQ, Matrix.mul_one, ← Matrix.mul_assoc, ← hcTE, Matrix.mul_assoc, h1, hcT1, Matrix.mul_one]
  have hA' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q'.map ιA) * J.map ιA * Q'.map ιA = 1 := by
    rw [cT_map, ← Matrix.map_mul, ← Matrix.map_mul, hE]
    exact hmap1
  have hg' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * J.map ιA *
      (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = J.map ιA := hg
  show cT (sigR σ (FiniteAdeleRing (𝓞 F) F))
      (Q.map ιA * (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * Q'.map ιA) * (1 : Matrix m m E).map ιA *
      (Q.map ιA * (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * Q'.map ιA) = (1 : Matrix m m E).map ιA
  rw [hmap1, Matrix.mul_one, hcTA, hcTA]
  calc cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q'.map ιA) *
        (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *
          cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA)) *
        (Q.map ιA * (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * Q'.map ιA)
      = cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q'.map ιA) *
          (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *
            (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA) * Q.map ιA) *
            (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) * Q'.map ιA := by
        simp only [Matrix.mul_assoc]
    _ = cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q'.map ιA) * J.map ιA * Q'.map ιA := by rw [hA, hg']
    _ = 1 := hA'
end Formalism.L2.GlobalTheoryTheory.Comp
