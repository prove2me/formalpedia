-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.frob_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:06.089793+00:00
-- url     : https://prove2.me/submissions/5d4a2992-ee81-42cc-bb6d-f696a178a99e

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frob_two
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_add
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
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hpi0 : 0 < ‖(l : K)‖) (hpi1 : ‖(l : K)‖ ≤ 1)
    {r : ι → ℝ} {wt : ℝ} {α : Type w} (s : Finset α) (A : α → MvPowerSeries ι K)
    (hA : ∀ i ∈ s, WtGe ‖(l : K)‖ r wt (A i)) :
    WtGe ‖(l : K)‖ r ((l : ℝ) * wt + 1) ((∑ i ∈ s, A i) ^ l - ∑ i ∈ s, A i ^ l) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow hl.ne_zero, sub_zero]
    exact wtGe_zero hpi0 r _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : WtGe ‖(l : K)‖ r wt (∑ i ∈ s, A i) :=
      wtGe_sum hpi0 s A fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have h1 := frob_two hl hpi0 (hA a (Finset.mem_insert_self a s)) hS
    have h2 := ih fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have h3 := wtGe_add hpi0 hpi1 h1 h2
    rw [min_self] at h3
    convert h3 using 1; ring
end Formalism.DworkPowerSeriesWeights
