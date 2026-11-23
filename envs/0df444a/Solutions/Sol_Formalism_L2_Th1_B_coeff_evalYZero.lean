-- Prove2me | solution 1 for Formalism.L2.Th1.B.coeff_evalYZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:47.945532+00:00
-- url     : https://prove2.me/submissions/395392c9-3f77-481a-8588-d5ac41ccd6d0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution (h : MvPowerSeries (Fin 2) K) (k : ℕ) :
    PowerSeries.coeff k (ev0 h) = coeff (Finsupp.single 0 k) h := by
  have hc : ∀ m : ℕ, MvPowerSeries.coeff (Finsupp.single () k) ((PowerSeries.X : PowerSeries K) ^ m) =
      if k = m then 1 else 0 := fun m => PowerSeries.coeff_X_pow k m
  show MvPowerSeries.coeff (Finsupp.single () k) (ev0 h) = _
  unfold ev0
  rw [MvPowerSeries.coeff_subst hasSubst_eval_second_zero, finsum_eq_single _ (Finsupp.single 0 k)]
  · rw [Finsupp.prod_single_index (by simp)]
    simp only [Matrix.cons_val_zero, hc, if_true, smul_eq_mul, mul_one]
  · intro d hd
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    by_cases h1 : d 1 = 0
    · have hd0 : k ≠ d 0 := by
        intro hk
        apply hd
        ext a
        fin_cases a <;> simp [h1, hk]
      rw [h1, pow_zero, mul_one, hc, if_neg hd0, smul_zero]
    · rw [zero_pow h1, mul_zero, map_zero, smul_zero]
end Formalism.L2.Th1.B
