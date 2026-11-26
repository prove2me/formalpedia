-- Prove2me | solution 1 for FirstPassageLinearTransport.shifted_linear_exp_Icc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:26.170575+00:00
-- url     : https://prove2.me/submissions/9fa8279a-7226-40aa-b6c5-06e6454589d7

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
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
import Theorems.Thm_FirstPassageLinearTransport_weighted_exp_Icc_le
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
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc₀c : c₀ ≤ c)
    {L U : ℕ} (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ))) *
        weightedTailConstant c₀ (c₀ / 2) := by
  have hc₀half : 0 < c₀ / 2 := by positivity
  have hhalf : c₀ / 2 < c₀ := by linarith
  let pref : ℝ :=
    ((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ)))
  have hterm : ∀ q ∈ Finset.Icc L U,
      ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
        pref * (((q - L + 1 : ℕ) : ℝ) *
          Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) := by
    intro q hq
    have hLq : L ≤ q := (Finset.mem_Icc.mp hq).1
    have hqSplit : q = L + (q - L) := by omega
    have hlinNat : q + 1 ≤ (L + 1) * (q - L + 1) := by
      rw [hqSplit]
      simp only [Nat.add_sub_cancel_left]
      nlinarith [Nat.zero_le (L * (q - L))]
    have hlin : ((q + 1 : ℕ) : ℝ) ≤
        ((L + 1 : ℕ) : ℝ) * ((q - L + 1 : ℕ) : ℝ) := by
      exact_mod_cast hlinNat
    have hexpSplit :
        Real.exp (-(c * (q : ℝ))) =
          Real.exp (-(c * (L : ℝ))) *
            Real.exp (-(c * ((q - L : ℕ) : ℝ))) := by
      have hqCast : (q : ℝ) = (L : ℝ) + ((q - L : ℕ) : ℝ) := by
        exact_mod_cast hqSplit
      rw [hqCast]
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpMono :
        Real.exp (-(c * ((q - L : ℕ) : ℝ))) ≤
          Real.exp (-(c₀ * ((q - L : ℕ) : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hj0 : (0 : ℝ) ≤ (q - L : ℕ) := by positivity
      nlinarith
    rw [hexpSplit]
    dsimp [pref]
    calc
      ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(c * (L : ℝ))) *
            Real.exp (-(c * ((q - L : ℕ) : ℝ)))) ≤
        (((L + 1 : ℕ) : ℝ) * ((q - L + 1 : ℕ) : ℝ)) *
          (Real.exp (-(c * (L : ℝ))) *
            Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) := by
          gcongr
      _ = (((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ)))) *
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) := by ring
  have hshift :
      ∑ q ∈ Finset.Icc L U,
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) =
        ∑ j ∈ Finset.Icc 0 (U - L),
          ((j + 1 : ℕ) : ℝ) * Real.exp (-(c₀ * (j : ℝ))) := by
    have hfin : Finset.range (U + 1 - L) = Finset.Icc 0 (U - L) := by
      ext j
      simp
      omega
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    change
      (∑ j ∈ Finset.range (U + 1 - L),
        ((j + 1 : ℕ) : ℝ) * Real.exp (-(c₀ * (j : ℝ)))) = _
    rw [hfin]
  have htail := weighted_exp_Icc_le hc₀half hhalf 0 (U - L)
  have hpref0 : 0 ≤ pref := by
    dsimp [pref]
    positivity
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      ∑ q ∈ Finset.Icc L U,
        pref * (((q - L + 1 : ℕ) : ℝ) *
          Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) :=
        Finset.sum_le_sum hterm
    _ = pref *
        ∑ q ∈ Finset.Icc L U,
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ = pref *
        ∑ j ∈ Finset.Icc 0 (U - L),
          ((j + 1 : ℕ) : ℝ) * Real.exp (-(c₀ * (j : ℝ))) := by
      rw [hshift]
    _ ≤ pref * weightedTailConstant c₀ (c₀ / 2) := by
      have htail' :
          ∑ j ∈ Finset.Icc 0 (U - L),
              ((j + 1 : ℕ) : ℝ) * Real.exp (-(c₀ * (j : ℝ))) ≤
            weightedTailConstant c₀ (c₀ / 2) := by
        simpa using htail
      exact mul_le_mul_of_nonneg_left htail' hpref0
    _ = ((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ))) *
        weightedTailConstant c₀ (c₀ / 2) := rfl
end FirstPassageLinearTransport
