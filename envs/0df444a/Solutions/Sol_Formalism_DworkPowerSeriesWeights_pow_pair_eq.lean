-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pow_pair_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:53.759744+00:00
-- url     : https://prove2.me/submissions/71a27d60-322b-4730-8d45-0440aae03395

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight

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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution [DecidableEq ι] (i j : ι) (x y : K) (a b : ℕ) :
    (MvPowerSeries.C x * MvPowerSeries.X i) ^ a * (MvPowerSeries.C y * MvPowerSeries.X j) ^ b =
      MvPowerSeries.monomial (Finsupp.single i a + Finsupp.single j b) (x ^ a * y ^ b) := by
  rw [mul_pow, mul_pow, ← map_pow, ← map_pow, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq]
  rw [mul_mul_mul_comm, ← map_mul]
  first
    | (rw [MvPowerSeries.monomial_mul_monomial, one_mul, ← MvPowerSeries.monomial_zero_eq_C_apply,
        MvPowerSeries.monomial_mul_monomial, zero_add, mul_one])
    | (simp [MvPowerSeries.monomial_mul_monomial, ← MvPowerSeries.monomial_zero_eq_C_apply])
end Formalism.DworkPowerSeriesWeights
