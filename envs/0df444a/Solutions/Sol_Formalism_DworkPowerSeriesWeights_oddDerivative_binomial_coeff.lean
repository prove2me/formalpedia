-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.oddDerivative_binomial_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:29.757644+00:00
-- url     : https://prove2.me/submissions/37c6bc34-a07e-4e25-b474-a000f8a80d34

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_coeff_subst
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_zero_series_binomial_form
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_oddIndicator_series_binomial_form
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_parity_series_binomial_form
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxM_false
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxM_true
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxN_bnxM
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_update_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_prod_choose
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d)
    (hs : s.val % 2 ≠ 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 ≠ 0 ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j)) (de2 be) = coeff n be * ((n s).choose j : K) := by
  have hk := bnx_update_le n s j hj
  unfold de2
  rw [map_sub, map_sub, oddIndicator_series_binomial_form, zero_series_binomial_form, parity_series_binomial_form, bnx_coeff_subst, bnx_coeff_subst, bnx_coeff_subst,
    bnxN_bnxM n _ hk]
  simp only [bnxM_false, bnxM_true]
  rw [bnx_prod_choose n s j hj (fun t => if t.val % 2 = 0 then (0 : K) else 1) (by simp [hs])]
  have hz0 : ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * (0 : K) ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    rw [Function.update_apply, if_pos rfl, zero_pow (by omega)]
    simp
  have hz2 : ∏ t, ((if t.val % 2 = 0 then (1 : K) else 0) ^ Function.update (⇑n) s j t *
      (if t.val % 2 = 0 then (0 : K) else 1) ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = 0 := by
    rcases hpos with hj0 | ⟨t, ht, hts, hnt⟩
    · apply Finset.prod_eq_zero (Finset.mem_univ s)
      rw [Function.update_apply, if_pos rfl, if_neg hs, zero_pow (by omega)]
      simp
    · apply Finset.prod_eq_zero (Finset.mem_univ t)
      rw [Function.update_apply, if_neg hts, if_neg ht, zero_pow hnt]
      simp
  rw [hz0, hz2, mul_zero, sub_zero, sub_zero]
end Formalism.DworkPowerSeriesWeights
