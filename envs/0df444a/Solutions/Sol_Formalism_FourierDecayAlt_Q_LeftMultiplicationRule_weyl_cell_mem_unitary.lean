-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.weyl_cell_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:53.532654+00:00
-- url     : https://prove2.me/submissions/27a1a344-c4f1-4adc-b509-fbd730aba818

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_tau_e
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_tau_es
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_sgn_e
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_sgn_es
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_off_support
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_off_support_row
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_column_isotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_column_dual_isotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_weyl_cell_apply_basis
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_weyl_cell_apply_dual_basis
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_mul_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_tau


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
theorem _root_.solution (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ UH (Hpk k r) := by
  have hsc : star c ≠ 0 := star_ne_zero.2 hc
  show (w1 k r l c)ᴴ * Hpk k r * w1 k r l c = Hpk k r
  ext p q
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [conjTranspose_apply, hpk_mul_apply]
  rw [hpk_row]
  by_cases hp1 : p = eI k r l
  · subst hp1
    rw [Finset.sum_eq_single (esI k r l)]
    · rw [reflection_column_isotropic, if_pos rfl, tau_es, sgn_es, weyl_cell_apply_basis, tau_e, sgn_e]
      by_cases hq : q = esI k r l
      · rw [if_pos hq, if_pos hq, one_mul, ← star_inv₀, ← star_mul, inv_mul_cancel₀ hc, star_one]
      · rw [if_neg hq, if_neg hq, mul_zero, mul_zero]
    · intro t _ ht; rw [reflection_column_isotropic, if_neg ht, star_zero, zero_mul]
    · simp
  · by_cases hp2 : p = esI k r l
    · subst hp2
      rw [Finset.sum_eq_single (eI k r l)]
      · rw [reflection_column_dual_isotropic, if_pos rfl, tau_e, sgn_e, weyl_cell_apply_dual_basis, tau_es, sgn_es]
        by_cases hq : q = eI k r l
        · rw [if_pos hq, if_pos hq, one_mul, star_inv₀, star_star, inv_mul_cancel₀ hc]
        · rw [if_neg hq, if_neg hq, mul_zero, mul_zero]
      · intro t _ ht; rw [reflection_column_dual_isotropic, if_neg ht, star_zero, zero_mul]
      · simp
    · have ht1 : tau k r p ≠ eI k r l := by
        intro h; apply hp2; rw [← tau_tau p, h, tau_e]
      have ht2 : tau k r p ≠ esI k r l := by
        intro h; apply hp1; rw [← tau_tau p, h, tau_es]
      rw [Finset.sum_eq_single p]
      · rw [reflection_off_support _ _ p p hp1 hp2, if_pos rfl, star_one, one_mul,
          reflection_off_support_row _ _ (tau k r p) q ht1 ht2]
        by_cases hq : q = tau k r p
        · rw [if_pos hq, if_pos hq.symm, mul_one]
        · rw [if_neg hq, if_neg (Ne.symm hq), mul_zero]
      · intro t _ ht; rw [reflection_off_support _ _ t p hp1 hp2, if_neg ht, star_zero, zero_mul]
      · simp
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
