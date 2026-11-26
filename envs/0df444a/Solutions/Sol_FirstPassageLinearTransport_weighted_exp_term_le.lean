-- Prove2me | solution 1 for FirstPassageLinearTransport.weighted_exp_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:47.757579+00:00
-- url     : https://prove2.me/submissions/acf35171-5696-453c-bc4a-aeeacb75e81d

import Mathlib.Algebra.Order.Field.GeomSum
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
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
    {c c' : ℝ} (hcc' : c' < c) (q : ℕ) :
    ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      (1 + 1 / (c - c')) * (Real.exp (-c')) ^ q := by
  let g := c - c'
  let C := 1 + 1 / g
  have hg : 0 < g := sub_pos.mpr hcc'
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hx0 : 0 ≤ g * (q : ℝ) := mul_nonneg hg.le (Nat.cast_nonneg q)
  have hpoly : ((q + 1 : ℕ) : ℝ) ≤ C * Real.exp (g * (q : ℝ)) := by
    have hexp := Real.add_one_le_exp (g * (q : ℝ))
    have hlinear : ((q + 1 : ℕ) : ℝ) ≤ C * (g * (q : ℝ) + 1) := by
      have hinv0 : 0 ≤ 1 / g := one_div_nonneg.mpr hg.le
      have hextra : 0 ≤ g * (q : ℝ) + 1 / g := add_nonneg hx0 hinv0
      have hrearrange :
          C * (g * (q : ℝ) + 1) =
            ((q + 1 : ℕ) : ℝ) + (g * (q : ℝ) + 1 / g) := by
        dsimp [C]
        field_simp [ne_of_gt hg]
        push_cast
        ring
      rw [hrearrange]
      exact le_add_of_nonneg_right hextra
    exact hlinear.trans (mul_le_mul_of_nonneg_left hexp hC0)
  calc
    ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
        (C * Real.exp (g * (q : ℝ))) *
          Real.exp (-(c * (q : ℝ))) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = C * Real.exp (-(c' * (q : ℝ))) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [g]
      congr 1
      ring
    _ = (1 + 1 / (c - c')) * (Real.exp (-c')) ^ q := by
      dsimp [C]
      rw [← Real.exp_nat_mul]
      congr 2
      ring
end FirstPassageLinearTransport
