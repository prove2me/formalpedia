-- Prove2me | solution 1 for Erdos684.upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:24:36.921387+00:00
-- url     : https://prove2.me/submissions/fac7e011-0f20-4b9b-9dd1-6ee51ba0b089

module
public import Definitions.Def_Erdos684_Lower
public import Definitions.Def_Erdos684_Averaging
public import Definitions.Def_Erdos684_Analytic
public import Definitions.Def_Erdos684ElementaryBounds_Solution
public import Theorems.Thm_Erdos684_averaged_smallPrimePart_lower
public import Theorems.Thm_Erdos684_eventually_averaging_gap
public import Theorems.Thm_Erdos684_eventually_upper_parameters
public import Theorems.Thm_Erdos684_smallPrimePart_pos


set_option autoImplicit false
@[expose] public section
public section
open Filter Real Finset
open scoped Topology
open Erdos684
namespace Erdos684
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop, ∃ k ≤ n,
      (k : ℝ) ≤ 514 * (log (n : ℝ)) ^ 2 ∧ n ^ 2 < smallPrimePart n k := by
  filter_upwards [eventually_upper_parameters, eventually_averaging_gap] with n hn hgap
  obtain ⟨_, hn0, hXn, _, _, _, _, _, _, _, hXlog⟩ := hn
  have hfinite := averaged_smallPrimePart_lower n (primeCutoff n) (windowLength n) hn0 hXn
  have hex : ∃ k ∈ Finset.Icc 1 (2 * primeCutoff n), n ^ 2 < smallPrimePart n k := by
    by_contra h
    push Not at h
    have hterm : ∀ k ∈ Finset.Icc 1 (2 * primeCutoff n),
        log (smallPrimePart n k : ℝ) ≤ 2 * log (n : ℝ) := by
      intro k hk
      have hu : smallPrimePart n k ≤ n ^ 2 := by
        have ht := h k hk
        omega
      have hr : (smallPrimePart n k : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hu
      have hl := Real.log_le_log (Nat.cast_pos.mpr (smallPrimePart_pos n k)) hr
      simpa only [Real.log_pow, Nat.cast_ofNat] using hl
    have hs := Finset.sum_le_sum hterm
    have hc : (∑ k ∈ Finset.Icc 1 (2 * primeCutoff n), 2 * log (n : ℝ)) =
        4 * (primeCutoff n : ℝ) * log n := by
      simp
      ring
    rw [hc] at hs
    linarith
  obtain ⟨k, hk, hku⟩ := hex
  have hkX := (Finset.mem_Icc.mp hk).2
  refine ⟨k, hkX.trans hXn, ?_, hku⟩
  have hkr : (k : ℝ) ≤ 2 * (primeCutoff n : ℝ) := by exact_mod_cast hkX
  exact hkr.trans hXlog
end Erdos684
