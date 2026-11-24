-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.exp_biv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:47.027102+00:00
-- url     : https://prove2.me/submissions/36af9986-0956-4106-95ae-373867ed60f3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExpSeriesBivariate Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate
variable {σ K : Type} [Field K] [Algebra ℚ K]
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
theorem _root_.solution :
    expS (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      expS (MvPowerSeries.X 0) * expS (MvPowerSeries.X 1) := by
  ext e
  unfold expS
  rw [PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  simp only [PowerSeries.coeff_exp]
  rw [← map_natCast (algebraMap ℚ K), ← map_mul, ← map_mul]
  congr 1
  have h := Nat.add_choose_mul_factorial_mul_factorial (e 0) (e 1)
  have h' : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    rw [Nat.choose_symm_add]; exact_mod_cast h
  have h0 : ((e 0).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h1 : ((e 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h2 : ((e 0 + e 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  field_simp
  linarith
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
