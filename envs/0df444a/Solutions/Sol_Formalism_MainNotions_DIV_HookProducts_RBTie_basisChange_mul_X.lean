-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.basisChange_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:19.142791+00:00
-- url     : https://prove2.me/submissions/07c64f91-6686-4be0-8283-593f763b36b3

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame

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
theorem _root_.solution (hXA : IsUnit (XA v).det) : cP b e v * X v = XA v * cU b XA X e v := by
  unfold cU
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXA, Matrix.one_mul]
end Formalism.MainNotions.DIV.HookProducts.RBTie
