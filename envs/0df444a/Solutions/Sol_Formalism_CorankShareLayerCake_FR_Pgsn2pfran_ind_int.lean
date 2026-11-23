-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:12.68541+00:00
-- url     : https://prove2.me/submissions/c04354b2-e658-4b30-a14c-cda2cd830129

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfran_ind_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Finset MeasureTheory
open Formalism.CorankShareLayerCake.FR.Pgsn2pfran
namespace Formalism.CorankShareLayerCake.FR.Pgsn2pfran
theorem _root_.solution (c HH : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ HH) :
    ∫ τ in (0:ℝ)..HH, (if τ < c then (1:ℝ) else 0) = c := by
  have hi1 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1:ℝ) else 0) volume 0 c :=
    (ind_anti c).intervalIntegrable
  have hi2 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1:ℝ) else 0) volume c HH :=
    (ind_anti c).intervalIntegrable
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [ae_iff]
    simp
  have h1 : ∫ τ in (0:ℝ)..c, (if τ < c then (1:ℝ) else 0) = ∫ τ in (0:ℝ)..c, (1:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hc0] at hmem
    have hxc : x < c := lt_of_le_of_ne hmem.2 hx
    simp [hxc]
  have h2 : ∫ τ in c..HH, (if τ < c then (1:ℝ) else 0) = ∫ τ in c..HH, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    simp [not_lt.mpr hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2]
  simp
end Formalism.CorankShareLayerCake.FR.Pgsn2pfran
