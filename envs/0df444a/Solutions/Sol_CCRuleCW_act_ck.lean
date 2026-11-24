-- Prove2me | solution 1 for CCRuleCW.act_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:18.030855+00:00
-- url     : https://prove2.me/submissions/d2687583-7412-4060-9cd0-d3806d89cadc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_act_eq
import Theorems.Thm_CCRuleCW_dir_contDiff
import Theorems.Thm_CCRuleCW_along

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
theorem _root_.solution (H : B.Mat k r → E) (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) : B.CkOn (⊤ : ℕ∞) (B.GV k r) (act o H) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hagree⟩ := hH g₀ hg₀
  refine ⟨U, fun g => fderiv ℝ f' g (dir o g), hU, hg₀U, ?_, ?_⟩
  · exact (hf'.fderiv_of_isOpen hU (by simp)).clm_apply (dir_contDiff o).contDiffOn
  · intro g hgU hg
    rw [act_eq]
    exact (along H hU hf' hagree o hX g hgU hg).deriv
end CCRuleCW
