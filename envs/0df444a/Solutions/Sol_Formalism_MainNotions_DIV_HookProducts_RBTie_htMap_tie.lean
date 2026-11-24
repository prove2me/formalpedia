-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.htMap_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:28.652991+00:00
-- url     : https://prove2.me/submissions/886d7982-a8c0-442a-a2ac-7e107d0f1e4c

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_opNormAt_tie

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
  {VN VR : Type} [AddCommGroup VN] [Module K VN] [AddCommGroup VR] [Module K VR]
  {ιN ιR : Type} [Fintype ιN] [DecidableEq ιN] [Fintype ιR] [DecidableEq ιR] {d n : ℕ}
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (bN : Basis ιN K VN) (XN : InfinitePlace K → Matrix ιN ιN ℂ) (bR : Basis ιR K VR)
    (XR : InfinitePlace K → Matrix ιR ιR ℂ) (Xc : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (eN : (Fin d → K) ≃ₗ[K] VN) (eR : (Fin n → K) ≃ₗ[K] VR)
    (hN : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bN XN v (eN x) (eN y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) Xc v x y)
    (hR : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bR XR v (eR x) (eR y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXN : ∀ v, IsUnit (XN v).det) (hXR : ∀ v, IsUnit (XR v).det) (hXc : ∀ v, IsUnit (Xc v).det)
    (hXE : ∀ v, IsUnit (XE v).det)
    (Bk : VN →ₗ[K] Module.Dual K VR) (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K))
    (hB : ∀ x y, Bk (eN x) (eR y) = B x y) :
    Formalism.HN.htMap bN XN bR.dualBasis (Formalism.HN.dualFrame XR) Bk =
      Formalism.HN.htMap (Pi.basisFun K (Fin d)) Xc (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) B := by
  unfold Formalism.HN.htMap
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [opNormAt_tie bN XN bR XR Xc XE eN eR hN hR hXN hXR hXc hXE Bk B hB v]
end Formalism.MainNotions.DIV.HookProducts.RBTie
