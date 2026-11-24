-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.cnorm_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:03.890776+00:00
-- url     : https://prove2.me/submissions/621b3c03-aa02-47ea-9460-9efedad71e90

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieMu
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
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (W : Matrix m n ℂ)
    (hW : Wᴴ * W = 1) (c : n → ℂ) : Formalism.HermitianLatticesTheory.cnorm (W *ᵥ c) = Formalism.HermitianLatticesTheory.cnorm c := by
  have key : ∀ {ι : Type} [Fintype ι] (u : ι → ℂ), ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
    intro ι _ u
    push_cast
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  have h : ((∑ i, ‖(W *ᵥ c) i‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [key, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hW,
      Matrix.one_mulVec]
  exact_mod_cast h
end Formalism.MainNotions.DIV.HookProducts.RBTie
