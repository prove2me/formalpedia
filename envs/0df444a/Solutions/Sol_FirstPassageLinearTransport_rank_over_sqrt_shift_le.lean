-- Prove2me | solution 1 for FirstPassageLinearTransport.rank_over_sqrt_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:01.920854+00:00
-- url     : https://prove2.me/submissions/7911ddad-8f81-4bc5-95d1-1b8e0fbbf6c1

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
    {L q : ℕ} (hL : 2 ≤ L) (hLq : L ≤ q) :
    ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) ≤
      3 * Real.sqrt L * ((q - L + 1 : ℕ) : ℝ) := by
  have hLm1posNat : 0 < L - 1 := by omega
  have hqm1posNat : 0 < q - 1 := by omega
  have hsL0 : 0 ≤ Real.sqrt (L : ℝ) := Real.sqrt_nonneg _
  have hsLm10 : 0 ≤ Real.sqrt ((L - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsLm1pos : 0 < Real.sqrt ((L - 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hLm1posNat)
  have hsQm1pos : 0 < Real.sqrt ((q - 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hqm1posNat)
  have hsDen : Real.sqrt ((L - 1 : ℕ) : ℝ) ≤
      Real.sqrt ((q - 1 : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le_sub_right hLq 1
  have hqSplit : q = L + (q - L) := by omega
  have hlinNat : q + 1 ≤ (L + 1) * (q - L + 1) := by
    rw [hqSplit]
    simp only [Nat.add_sub_cancel_left]
    nlinarith [Nat.zero_le (L * (q - L))]
  have hlin : ((q + 1 : ℕ) : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) * ((q - L + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlinNat
  have hbase : ((L + 1 : ℕ) : ℝ) /
      Real.sqrt ((L - 1 : ℕ) : ℝ) ≤ 3 * Real.sqrt L := by
    apply (div_le_iff₀ hsLm1pos).2
    have hsLm1sq := Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ ((L - 1 : ℕ) : ℝ))
    have hlinL : ((L + 1 : ℕ) : ℝ) ≤
        3 * ((L - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show L + 1 ≤ 3 * (L - 1) by omega)
    have hsLm1L : Real.sqrt ((L - 1 : ℕ) : ℝ) ≤ Real.sqrt L := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Nat.sub_le L 1)
    calc
      ((L + 1 : ℕ) : ℝ) ≤ 3 * ((L - 1 : ℕ) : ℝ) := hlinL
      _ = 3 * (Real.sqrt ((L - 1 : ℕ) : ℝ)) ^ 2 := by
        congr 1
        exact hsLm1sq.symm
      _ = 3 * Real.sqrt ((L - 1 : ℕ) : ℝ) *
          Real.sqrt ((L - 1 : ℕ) : ℝ) := by ring
      _ ≤ 3 * Real.sqrt L * Real.sqrt ((L - 1 : ℕ) : ℝ) := by
        gcongr
  have hrecip : 1 / Real.sqrt ((q - 1 : ℕ) : ℝ) ≤
      1 / Real.sqrt ((L - 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hsLm1pos hsDen
  calc
    ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) =
        ((q + 1 : ℕ) : ℝ) *
          (1 / Real.sqrt ((q - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (((L + 1 : ℕ) : ℝ) * ((q - L + 1 : ℕ) : ℝ)) *
          (1 / Real.sqrt ((L - 1 : ℕ) : ℝ)) := by
      gcongr
    _ = (((L + 1 : ℕ) : ℝ) /
          Real.sqrt ((L - 1 : ℕ) : ℝ)) *
        ((q - L + 1 : ℕ) : ℝ) := by ring
    _ ≤ 3 * Real.sqrt L * ((q - L + 1 : ℕ) : ℝ) := by
      gcongr
end FirstPassageLinearTransport
