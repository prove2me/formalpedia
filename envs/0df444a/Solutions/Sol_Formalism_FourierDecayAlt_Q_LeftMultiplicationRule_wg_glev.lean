-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.wg_glev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:32:20.836711+00:00
-- url     : https://prove2.me/submissions/dcb10912-c4fa-491d-8288-644f4e419f61

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_weyl_cell_mem_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_fixes_basis_vector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_eI_val
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_esI_val
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution (l : Fin r) (c : ℂ) (hc : c ≠ 0) {g₁ : Mx k r} (hg : g₁ ∈ Glev k r l.succ) :
    w1 k r l c * g₁ ∈ Glev k r l.castSucc := by
  refine ⟨uh_mul (weyl_cell_mem_unitary l c hc) hg.1, fun a ha => ?_⟩
  have hal : a.val < l.val := by simpa using ha
  have ha' : a.val < l.succ.val := by simp; omega
  have hl := l.isLt
  obtain ⟨h1, h2⟩ := hg.2 a ha'
  constructor
  · rw [← Matrix.mulVec_mulVec, h1]
    apply reflection_fixes_basis_vector
    · intro h; have := congrArg Fin.val h; rw [eI_val, eI_val] at this; omega
    · intro h; have := congrArg Fin.val h; rw [eI_val, esI_val] at this; omega
  · rw [← Matrix.mulVec_mulVec, h2]
    apply reflection_fixes_basis_vector
    · intro h; have := congrArg Fin.val h; rw [esI_val, eI_val] at this; omega
    · intro h; have := congrArg Fin.val h; rw [esI_val, esI_val] at this; omega
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
