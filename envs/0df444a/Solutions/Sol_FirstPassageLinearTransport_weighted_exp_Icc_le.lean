-- Prove2me | solution 1 for FirstPassageLinearTransport.weighted_exp_Icc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:03.061573+00:00
-- url     : https://prove2.me/submissions/c845fa3a-c7f7-493d-86b2-a18d783d932c

import Mathlib.Algebra.Order.Field.GeomSum
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Theorems.Thm_FirstPassageLinearTransport_weighted_exp_term_le
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {c c' : ℝ} (hc' : 0 < c') (hcc' : c' < c) (L U : ℕ) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      weightedTailConstant c c' * Real.exp (-(c' * (L : ℝ))) := by
  let a := Real.exp (-c')
  let C := 1 + 1 / (c - c')
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a < 1 := by
    dsimp [a]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsum :
      ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
        ∑ q ∈ Finset.Icc L U, C * a ^ q := by
    apply Finset.sum_le_sum
    intro q hq
    simpa [C, a] using weighted_exp_term_le hcc' q
  have hgeom :
      ∑ q ∈ Finset.Icc L U, a ^ q ≤ a ^ L / (1 - a) := by
    rw [← Finset.Ico_succ_right_eq_Icc]
    exact geom_sum_Ico_le_of_lt_one ha0 ha1
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
        ∑ q ∈ Finset.Icc L U, C * a ^ q := hsum
    _ = C * ∑ q ∈ Finset.Icc L U, a ^ q := by
      rw [Finset.mul_sum]
    _ ≤ C * (a ^ L / (1 - a)) := by
      exact mul_le_mul_of_nonneg_left hgeom (by
        dsimp [C]
        exact add_nonneg zero_le_one (one_div_nonneg.mpr (sub_nonneg.mpr hcc'.le)))
    _ = weightedTailConstant c c' * Real.exp (-(c' * (L : ℝ))) := by
      unfold weightedTailConstant
      dsimp [C, a]
      rw [← Real.exp_nat_mul]
      ring
end FirstPassageLinearTransport
