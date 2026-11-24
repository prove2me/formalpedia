-- Prove2me | solution 1 for CCRuleCW.smul_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:22:54.474259+00:00
-- url     : https://prove2.me/submissions/8080d379-428d-487a-8f7a-ecb91a376296

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate Nat ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution (Q : B.Mat k r → ℂ) (hQ : ContDiff ℝ ∞ Q) (H : B.Mat k r → E)
    (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H) : B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => Q g • H g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hagree⟩ := hH g₀ hg₀
  refine ⟨U, fun g => Q g • f' g, hU, hg₀U, hQ.contDiffOn.smul hf', ?_⟩
  intro g hgU hg
  simp only [hagree g hgU hg]
end CCRuleCW
