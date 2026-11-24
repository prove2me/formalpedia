-- Prove2me | solution 1 for CCRuleCW.Hpk_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:00:00.495168+00:00
-- url     : https://prove2.me/submissions/a9add2c4-6bc7-4567-8ff9-7804035264af

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine

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
namespace CCRuleCW
theorem _root_.solution (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r ≠ 0 := by
  intro h
  have := congrFun (congrFun h ⟨r, by omega⟩) ⟨r, by omega⟩
  simp only [Formalism.QuantumDeterminants.Hpk, Matrix.zero_apply] at this
  rw [if_neg (by simp), if_neg (by simp), if_pos (by simp)] at this
  split_ifs at this <;> norm_num at this
end CCRuleCW
