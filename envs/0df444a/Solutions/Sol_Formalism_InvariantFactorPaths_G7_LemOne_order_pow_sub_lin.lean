-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.order_pow_sub_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.648072+00:00
-- url     : https://prove2.me/submissions/a5767f11-75ea-41be-9192-37686f6c1397

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_order_sub_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (F ^ n - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : F ^ (n + 1) - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ (n + 1) =
        F * (F ^ n - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n) +
          (F - (MvPowerSeries.X 0 + MvPowerSeries.X 1)) *
            (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) MvPowerSeries.min_order_le_add
    · refine le_trans ?_ MvPowerSeries.le_order_mul
      have h1 : (1 : ℕ∞) ≤ F.order := MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hF0
      calc ((n + 1 + 1 : ℕ) : ℕ∞) = 1 + ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ _ := add_le_add h1 ih
    · refine le_trans ?_ MvPowerSeries.le_order_mul
      have h2 := order_sub_lin hF0 hF1
      have h3 : (n : ℕ∞) ≤ ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ n).order :=
        MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n (by simp)
      calc ((n + 1 + 1 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) + (n : ℕ∞) := by push_cast; ring
        _ ≤ _ := add_le_add h2 h3
end Formalism.InvariantFactorPaths.G7.LemOne
