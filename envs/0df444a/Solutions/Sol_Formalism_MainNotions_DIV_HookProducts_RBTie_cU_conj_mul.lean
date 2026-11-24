-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.cU_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:31:44.192895+00:00
-- url     : https://prove2.me/submissions/34fd0135-f46b-449d-b7b0-5876c5d551c5

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_gram_tie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
variable (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
  (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hX : IsUnit (X v).det) : (cU b XA X e v)ᴴ * cU b XA X e v = 1 := by
  have hg := gram_tie b XA X e h v
  have hinv : (X v)⁻¹ * X v = 1 := Matrix.nonsing_inv_mul _ hX
  calc (cU b XA X e v)ᴴ * cU b XA X e v
      = (X v)ᴴ * (((XA v)⁻¹ * cP b e v)ᴴ * ((XA v)⁻¹ * cP b e v)) * X v := by
        simp only [cU, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (X v)ᴴ * (((X v)⁻¹)ᴴ * (X v)⁻¹) * X v := by rw [hg]
    _ = ((X v)⁻¹ * X v)ᴴ * ((X v)⁻¹ * X v) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hinv, Matrix.conjTranspose_one, Matrix.mul_one]
end Formalism.MainNotions.DIV.HookProducts.RBTie
