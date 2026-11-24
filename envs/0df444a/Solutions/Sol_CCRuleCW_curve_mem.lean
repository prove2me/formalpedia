-- Prove2me | solution 1 for CCRuleCW.curve_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:18.350695+00:00
-- url     : https://prove2.me/submissions/5b679e92-3d21-4e28-a204-edd91e0a7aed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Theorems.Thm_CCRuleCW_UH_mul
import Theorems.Thm_CCRuleCW_exp_mem_UH
import Theorems.Thm_CCRuleCW_lie_smul


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
theorem _root_.solution (o : Bool × B.Mat k r) (g : B.Mat k r) (t : ℝ) (hX : B.inLie k r o.2)
    (hg : g ∈ B.GV k r) : curve o g t ∈ B.GV k r := by
  rcases o with ⟨_ | _, X⟩
  · exact UH_mul _ _ _ hg (exp_mem_UH _ _ (lie_smul _ X hX t))
  · have : -((t : ℂ) • X) = ((-t : ℝ) : ℂ) • X := by push_cast; rw [neg_smul]
    show NormedSpace.exp (-((t : ℂ) • X)) * g ∈ B.GV k r
    rw [this]
    exact UH_mul _ _ _ (exp_mem_UH _ _ (lie_smul _ X hX (-t))) hg
end CCRuleCW
