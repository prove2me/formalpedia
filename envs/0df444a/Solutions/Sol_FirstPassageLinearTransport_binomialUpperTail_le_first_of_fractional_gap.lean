-- Prove2me | solution 1 for FirstPassageLinearTransport.binomialUpperTail_le_first_of_fractional_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:45.670697+00:00
-- url     : https://prove2.me/submissions/7a6551f0-52e3-4b3d-95e1-3c944f557115

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_binomialUpperTail_weighted_le
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t₀ : ℝ} (ht₀ : 0 < t₀) {r k : ℕ}
    (hr : 0 < r) (hkr : k ≤ r)
    (hgap : (r : ℝ) * (1 / 2 + t₀) ≤ (k : ℝ)) :
    (binomialUpperTail r k : ℝ) ≤
      (1 / (2 * t₀)) * (r.choose k : ℝ) := by
  have hhalf : r < 2 * k := by
    exact_mod_cast (show (r : ℝ) < 2 * (k : ℝ) by
      have hrR : 0 < (r : ℝ) := by positivity
      nlinarith)
  have hweighted := binomialUpperTail_weighted_le hkr hhalf
  have htail0 : 0 ≤ (binomialUpperTail r k : ℝ) := by positivity
  have hchoose0 : 0 ≤ (r.choose k : ℝ) := by positivity
  have hcoeff :
      2 * t₀ * (r : ℝ) ≤ ((2 * k : ℕ) : ℝ) - (r : ℝ) := by
    push_cast
    nlinarith
  have hleft := mul_le_mul_of_nonneg_right hcoeff htail0
  have hright :
      (k : ℝ) * (r.choose k : ℝ) ≤
        (r : ℝ) * (r.choose k : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkr) hchoose0
  have hcombined :
      (r : ℝ) * (2 * t₀ * (binomialUpperTail r k : ℝ)) ≤
        (r : ℝ) * (r.choose k : ℝ) := by
    calc
      (r : ℝ) * (2 * t₀ * (binomialUpperTail r k : ℝ)) =
          (2 * t₀ * (r : ℝ)) * (binomialUpperTail r k : ℝ) := by ring
      _ ≤ (((2 * k : ℕ) : ℝ) - (r : ℝ)) *
          (binomialUpperTail r k : ℝ) := hleft
      _ ≤ (k : ℝ) * (r.choose k : ℝ) := hweighted
      _ ≤ (r : ℝ) * (r.choose k : ℝ) := hright
  have hcancel :
      2 * t₀ * (binomialUpperTail r k : ℝ) ≤ (r.choose k : ℝ) :=
    (mul_le_mul_iff_of_pos_left (show 0 < (r : ℝ) by positivity)).mp hcombined
  calc
    (binomialUpperTail r k : ℝ) ≤
        (r.choose k : ℝ) / (2 * t₀) :=
      (le_div_iff₀ (mul_pos (by norm_num) ht₀)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel)
    _ = (1 / (2 * t₀)) * (r.choose k : ℝ) := by ring
end FirstPassageLinearTransport
