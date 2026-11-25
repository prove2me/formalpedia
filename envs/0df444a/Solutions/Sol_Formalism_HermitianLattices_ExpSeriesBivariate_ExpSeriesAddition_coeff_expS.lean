-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.coeff_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:06:09.334218+00:00
-- url     : https://prove2.me/submissions/0374811f-b7dd-4fb7-bc4b-33d5d815c758

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_low_pow

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
theorem _root_.solution (f : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0)
    (d : σ →₀ ℕ) (N : ℕ) (hN : d.degree < N) :
    MvPowerSeries.coeff d (expS f) =
      ∑ n ∈ range N, algebraMap ℚ K (1 / n.factorial) * MvPowerSeries.coeff d (f ^ n) := by
  unfold expS
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [PowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset _ (s := range N) ?_]
  · apply Finset.sum_congr rfl
    intro n _
    first
    | rw [PowerSeries.coeff_exp, smul_eq_mul]
    | simp [PowerSeries.coeff_exp]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hnN
    push_neg at hnN
    apply hn
    rw [low_pow hf n d (by omega), smul_zero]
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
