-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.ex_mem_of_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:42:22.278993+00:00
-- url     : https://prove2.me/submissions/8855d039-a946-46e2-8230-6b10d5405bdf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Theorems.Thm_CCRuleCW_exp_mem_UH


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI.PhMeasCore
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution {Hm X : Mat n} (hX : Xᴴ * Hm + Hm * X = 0) (t : ℝ) :
    (ex X t)ᴴ * Hm * ex X t = Hm := by
  refine CCRuleCW.exp_mem_UH Hm _ ?_
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]
end CompanionTheory.D.Upq.Sm
