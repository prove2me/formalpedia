-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.frob_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:39.013744+00:00
-- url     : https://prove2.me/submissions/79c23a2e-47c7-4cd1-a6e8-b0c4b83162a8

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_congr
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_le_of_dvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mul_natCast
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_sum


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
variable [IsUltrametricDist K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hpi0 : 0 < ‖(l : K)‖) {r : ι → ℝ} {wt : ℝ}
    {A B : MvPowerSeries ι K} (hA : WtGe ‖(l : K)‖ r wt A) (hB : WtGe ‖(l : K)‖ r wt B) :
    WtGe ‖(l : K)‖ r ((l : ℝ) * wt + 1) ((A + B) ^ l - A ^ l - B ^ l) := by
  obtain ⟨k, hk⟩ : ∃ k, l = k + 1 + 1 := ⟨l - 2, by have := hl.two_le; omega⟩
  have key : (A + B) ^ l - A ^ l - B ^ l = ∑ m ∈ Finset.range (k + 1),
      A ^ (m + 1) * B ^ (l - (m + 1)) * (l.choose (m + 1) : MvPowerSeries ι K) := by
    subst hk
    rw [add_pow, Finset.sum_range_succ _ (k + 1 + 1), Finset.sum_range_succ' _ (k + 1)]
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, pow_zero,
      Nat.cast_one, mul_one, one_mul]
    abel
  rw [key]
  refine wtGe_sum hpi0 _ _ fun m hm => ?_
  have hm' : m + 1 < l := by rw [Finset.mem_range] at hm; omega
  have hdv : l ∣ l.choose (m + 1) := hl.dvd_choose_self (by omega) hm'
  refine wtGe_congr ?_ (wtGe_mul_natCast hpi0 (wtGe_mul hpi0 (wtGe_pow hpi0 hA (m + 1))
    (wtGe_pow hpi0 hB (l - (m + 1)))) (norm_natCast_le_of_dvd hdv))
  rw [Nat.cast_sub hm'.le]; push_cast; ring
end Formalism.DworkPowerSeriesWeights
