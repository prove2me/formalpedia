-- Prove2me | solution 1 for FirstPassageLinearTransport.log_four_thirds_gt_296_div_1029
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:28.59086+00:00
-- url     : https://prove2.me/submissions/ec0fa2bc-e0a8-49bb-acc2-870a715953d3

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum.BigOperators
import Definitions.Def_FirstPassageLinearTransport_Scalar
import Definitions.Def_FirstPassageLinearTransport_Constants
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    (296 / 1029 : ℝ) < Real.log (4 / 3) := by
  let f : ℕ → ℝ := fun k =>
    2 * (1 / (2 * k + 1 : ℝ)) * (1 / 7 : ℝ) ^ (2 * k + 1)
  have hsum : HasSum f (Real.log (1 + (3 : ℝ)⁻¹)) := by
    simpa [f, show (2 * (3 : ℝ) + 1) = 7 by norm_num] using
      (Real.hasSum_log_one_add_inv (a := (3 : ℝ)) (by norm_num))
  have hnonneg : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    positivity
  have hpartial : ∑ k ∈ Finset.range 3, f k ≤ ∑' k, f k :=
    hsum.summable.sum_le_tsum (Finset.range 3) (fun k _ => hnonneg k)
  rw [hsum.tsum_eq] at hpartial
  have hlog : Real.log (1 + (3 : ℝ)⁻¹) = Real.log (4 / 3) := by
    congr 1
    norm_num
  rw [hlog] at hpartial
  norm_num [f] at hpartial ⊢
  exact lt_of_lt_of_le (by norm_num) hpartial
end FirstPassageLinearTransport
