-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_lin_pow_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:02.362812+00:00
-- url     : https://prove2.me/submissions/5bab8cd4-779a-4e0b-b8a3-1482e014f1ff

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_lin_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_single_add_single_eq

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
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] {x y : σ} (hxy : x ≠ y)
    (a b : K) (k i j : ℕ) :
    coeff (Finsupp.single x i + Finsupp.single y j) ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      if i + j = k then a ^ i * b ^ j * (k.choose i : K) else 0 := by
  rw [bnx_lin_pow]
  simp_rw [bnx_single_add_single_eq hxy]
  split_ifs with hk
  · rw [Finset.sum_eq_single i]
    · have hj : k - i = j := by omega
      rw [if_pos ⟨rfl, hj⟩, hj]
    · intro r _ hr
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hr h1
    · intro hi
      simp only [Finset.mem_range] at hi
      omega
  · refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    simp only [Finset.mem_range] at hr
    omega
end Formalism.DworkPowerSeriesWeights
