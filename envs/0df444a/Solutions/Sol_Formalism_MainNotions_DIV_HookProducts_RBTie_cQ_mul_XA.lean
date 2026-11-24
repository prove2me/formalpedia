-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.cQ_mul_XA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:23.511874+00:00
-- url     : https://prove2.me/submissions/0b70f825-6995-4501-82bb-0815ffe5fed4

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cU_conj_eq

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
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cQ b e v * XA v = X v * (cU b XA X e v)ᴴ := by
  rw [cU_conj_eq b XA X e v h hXA hX]
  unfold cV
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.one_mul]
end Formalism.MainNotions.DIV.HookProducts.RBTie
