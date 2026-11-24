-- Prove2me | solution 1 for CCRuleCW.exp_mem_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:21:19.427602+00:00
-- url     : https://prove2.me/submissions/93453764-c559-4a2d-82ec-a46af5a86d81

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Theorems.Thm_CCRuleCW_exp_intertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate Nat
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
namespace CCRuleCW
theorem _root_.solution (H Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ Formalism.QuantumDeterminants.UH H := by
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  have h1 : Yᴴ * H = H * (-Y) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hY
  rw [← Matrix.exp_conjTranspose, exp_intertwine _ _ _ h1, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]
end CCRuleCW
