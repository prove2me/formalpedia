-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmOne_lin_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:14.489677+00:00
-- url     : https://prove2.me/submissions/be239e9a-bcf7-4179-a669-db87a726383e

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_single


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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v} [Fintype ι]
    {pi : ℝ} (h0 : 0 < pi) (c : ι → K) (hc : ∀ i, ‖c i‖ ≤ 1) (t : ℝ) :
    WtGe pi (fun _ : ι => t) t (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) := by
  classical
  intro n
  unfold MonoWtGe
  rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases hn : ∃ i, n = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := hn
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one, asmR_dot_single]
      simp only [Nat.cast_one, one_mul, sub_self, Real.rpow_zero]
      exact hc i
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      exact hj ((Finsupp.single_left_injective one_ne_zero) h).symm
    · simp
  · push_neg at hn
    rw [Finset.sum_eq_zero (fun i _ => by rw [if_neg (hn i), mul_zero]), norm_zero]
    exact Real.rpow_nonneg h0.le _
end Formalism.DworkPowerSeriesWeights
