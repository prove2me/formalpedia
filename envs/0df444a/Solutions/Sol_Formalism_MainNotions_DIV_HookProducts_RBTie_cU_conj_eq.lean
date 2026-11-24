-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.cU_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:58.521728+00:00
-- url     : https://prove2.me/submissions/b7fe8e66-4578-42ed-939a-9e8c7bf3be8e

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cU_conj_mul
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cU_mul_cV

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
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : (cU b XA X e v)ᴴ = cV b XA X e v := by
  calc (cU b XA X e v)ᴴ = (cU b XA X e v)ᴴ * (cU b XA X e v * cV b XA X e v) := by
        rw [cU_mul_cV b XA X e v hXA hX, Matrix.mul_one]
    _ = ((cU b XA X e v)ᴴ * cU b XA X e v) * cV b XA X e v := (Matrix.mul_assoc _ _ _).symm
    _ = cV b XA X e v := by rw [cU_conj_mul b XA X e v h hX, Matrix.one_mul]
end Formalism.MainNotions.DIV.HookProducts.RBTie
