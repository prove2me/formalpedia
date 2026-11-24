-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.glev_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:10:54.88425+00:00
-- url     : https://prove2.me/submissions/36ee998e-731f-46b9-af95-304250bb4823

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_tau_e
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_tau_es
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_esI_val
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_of_fix
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_row_of_fixed_col


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
theorem _root_.solution {l : Fin r} {g : Mx k r} (hg : g ∈ Glev k r l.succ) (p : Fin (2 * r + k + 1))
    (hp : ¬ (l.val < p.val ∧ p.val < 2 * r + k - l.val)) :
    (∀ q, g p q = if p = q then 1 else 0) ∧ (∀ q, g q p = if q = p then 1 else 0) := by
  have hl := l.isLt
  by_cases h1 : p.val ≤ l.val
  · let a : Fin r := ⟨p.val, by omega⟩
    have hpa : eI k r a = p := Fin.ext rfl
    have ha : a.val < l.succ.val := by simp [a]; omega
    have hc1 := col_of_fix (hg.2 a ha).1
    have hc2 := col_of_fix (hg.2 a ha).2
    have hrow := row_of_fixed_col hg.1 (esI k r a) hc2
    rw [tau_es, hpa] at hrow
    rw [hpa] at hc1
    exact ⟨hrow, hc1⟩
  · let a : Fin r := ⟨2 * r + k - p.val, by omega⟩
    have hpa : esI k r a = p := by apply Fin.ext; rw [esI_val]; simp [a]; omega
    have ha : a.val < l.succ.val := by simp [a]; omega
    have hc1 := col_of_fix (hg.2 a ha).1
    have hc2 := col_of_fix (hg.2 a ha).2
    have hrow := row_of_fixed_col hg.1 (eI k r a) hc1
    rw [tau_e, hpa] at hrow
    rw [hpa] at hc2
    exact ⟨hrow, hc2⟩
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
