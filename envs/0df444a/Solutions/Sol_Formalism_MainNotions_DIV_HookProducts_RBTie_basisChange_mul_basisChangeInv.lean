-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.basisChange_mul_basisChangeInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:02.463886+00:00
-- url     : https://prove2.me/submissions/189f2850-8583-45cf-ac64-a14375787e13

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
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : cP b e v * cQ b e v = 1 := by
  unfold cP cQ
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp]
  simp
end Formalism.MainNotions.DIV.HookProducts.RBTie
