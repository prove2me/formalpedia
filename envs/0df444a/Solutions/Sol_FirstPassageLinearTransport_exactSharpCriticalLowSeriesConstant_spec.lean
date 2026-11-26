-- Prove2me | solution 1 for FirstPassageLinearTransport.exactSharpCriticalLowSeriesConstant_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:09.199803+00:00
-- url     : https://prove2.me/submissions/6fc395cd-ed1d-4887-acdd-a5ee4e98c641

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Theorems.Thm_FirstPassageLinearTransport_exact_sharp_critical_low_series_Icc_le
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
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {b₀ Cpref : ℝ} (hb₀ : 0 < b₀) (hCpref : 0 ≤ Cpref) :
    0 < exactSharpCriticalLowSeriesConstant b₀ Cpref ∧
      ∀ {b : ℝ}, b₀ ≤ b → ∀ {L U : ℕ},
      2 ≤ L → L ≤ U →
      ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
                Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) ≤
        exactSharpCriticalLowSeriesConstant b₀ Cpref *
          (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by
  let Kdy := weightedTailConstant (Real.log 2) (Real.log 2 / 2)
  let Kent := 3 * Cpref * weightedTailConstant b₀ (b₀ / 2)
  have hKdy0 : 0 ≤ Kdy := by
    dsimp [Kdy, weightedTailConstant]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hgap : 0 < Real.log 2 - Real.log 2 / 2 := by linarith
    have hden : 0 < 1 - Real.exp (-(Real.log 2 / 2)) := by
      have : Real.exp (-(Real.log 2 / 2)) < 1 :=
        Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    exact div_nonneg (by positivity) hden.le
  have hKent0 : 0 ≤ Kent := by
    dsimp [Kent, weightedTailConstant]
    have hgap : 0 < b₀ - b₀ / 2 := by linarith
    have hden : 0 < 1 - Real.exp (-(b₀ / 2)) := by
      have : Real.exp (-(b₀ / 2)) < 1 :=
        Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    exact mul_nonneg (mul_nonneg (by norm_num) hCpref)
      (div_nonneg (by positivity) hden.le)
  let K := exactSharpCriticalLowSeriesConstant b₀ Cpref
  have hK : 0 < K := by
    dsimp [K, exactSharpCriticalLowSeriesConstant, Kdy, Kent]
    exact add_pos_of_nonneg_of_pos
      (le_max_of_le_left hKdy0) zero_lt_one
  refine ⟨hK, ?_⟩
  intro b hb₀b L U hL hLU
  have htail := exact_sharp_critical_low_series_Icc_le
    hb₀ hb₀b hCpref hL hLU
  have hdyK : Kdy ≤ K := by
    dsimp [K, exactSharpCriticalLowSeriesConstant, Kdy, Kent]
    exact (le_max_left Kdy Kent).trans (by linarith)
  have hentK : Kent ≤ K := by
    dsimp [K, exactSharpCriticalLowSeriesConstant, Kdy, Kent]
    exact (le_max_right Kdy Kent).trans (by linarith)
  have hbase0 : 0 ≤
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) := by
    positivity
  have hentbase0 : 0 ≤
      Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
    positivity
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) ≤
      Kdy * (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ)))) +
        Kent * (Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by
        simpa [Kdy, Kent, mul_assoc] using htail
    _ ≤ K * (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ)))) +
        K * (Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hdyK hbase0)
        (mul_le_mul_of_nonneg_right hentK hentbase0)
    _ = K * (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by ring
end FirstPassageLinearTransport
