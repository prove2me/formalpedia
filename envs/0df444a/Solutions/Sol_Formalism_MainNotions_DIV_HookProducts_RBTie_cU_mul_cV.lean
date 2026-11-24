-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.cU_mul_cV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:14.844992+00:00
-- url     : https://prove2.me/submissions/a8185fed-4e09-4e04-8eae-061698466827

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_basisChange_mul_basisChangeInv

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
theorem _root_.solution (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cU b XA X e v * cV b XA X e v = 1 := by
  calc cU b XA X e v * cV b XA X e v
      = (XA v)⁻¹ * (cP b e v * (X v * (X v)⁻¹) * cQ b e v) * XA v := by
        simp only [cU, cV, Matrix.mul_assoc]
    _ = (XA v)⁻¹ * XA v := by
        rw [Matrix.mul_nonsing_inv _ hX, Matrix.mul_one, basisChange_mul_basisChangeInv, Matrix.mul_one]
    _ = 1 := Matrix.nonsing_inv_mul _ hXA
end Formalism.MainNotions.DIV.HookProducts.RBTie
