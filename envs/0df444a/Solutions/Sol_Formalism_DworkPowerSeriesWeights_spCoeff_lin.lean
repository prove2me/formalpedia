-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spCoeff_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:20.145884+00:00
-- url     : https://prove2.me/submissions/08d0b784-4aac-4ad5-8658-211f583f767d

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
variable (lt : ι → σ) (N : σ → ι → R)
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (s : σ) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) =
      ∑ k, N s k * if n = Finsupp.single k 1 then 1 else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
end Formalism.DworkPowerSeriesWeights
