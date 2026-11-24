-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.quad_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:18.347918+00:00
-- url     : https://prove2.me/submissions/de77996c-ee17-4942-92c5-683e34808bf6

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → K) (k : ℕ) :
    (∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) :
      MvPowerSeries (Bool × ι) K) ^ k =
    ∑ n ∈ Finset.piAntidiag Finset.univ k, (Nat.multinomial Finset.univ n : MvPowerSeries (Bool × ι) K) *
      MvPowerSeries.monomial (pairExp n) (∏ i, u i ^ n i) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  unfold pairExp
  rw [← MvPowerSeries.prod_monomial]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← MvPowerSeries.monomial_pow]
  congr 1
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]
  simp
end Formalism.DworkPowerSeriesWeights
