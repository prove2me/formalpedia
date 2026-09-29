-- Prove2me | solution 1 for Erdos183.divergentRamseyRoot
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:35:36.661088+00:00
-- url     : https://prove2.me/submissions/62615678-2a98-4e57-a5a4-608d340c34a3

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_Erdos183_allColourPaletteRamsey_exponential_bound_sharp
import Theorems.Thm_Erdos183_paletteColourCount_mono
import Theorems.Thm_Erdos183_paletteColourCount_three

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution :
    Filter.Tendsto
      (fun k : ℕ =>
        (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro bound
  let minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
  have hminimum : 3 ≤ minimum := Nat.le_max_left _ _
  filter_upwards [Filter.eventually_ge_atTop (paletteColourCount minimum)]
    with k hk
  have hklarge : paletteColourCount 3 ≤ k :=
    (paletteColourCount_mono (by norm_num) hminimum).trans hk
  obtain ⟨H, _, _, hupper, hramsey⟩ :=
    allColourPaletteRamsey_exponential_bound_sharp k hklarge
  have hstage : minimum ≤ H := by
    by_contra h
    have hcolour := paletteColourCount_mono
      (by omega : 1 ≤ H + 1) (by omega : H + 1 ≤ minimum)
    omega
  have hkreal : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le
      (by norm_num [paletteColourCount_three] : 0 < paletteColourCount 3)
      hklarge)
  calc
    bound ≤ (H : ℝ) / Real.exp 38 := by
      apply (le_div_iff₀ (Real.exp_pos 38)).mpr
      exact (Nat.le_ceil _).trans (by
        exact_mod_cast
          (Nat.le_max_right 3 ⌈bound * Real.exp 38⌉₊).trans hstage)
    _ ≤ (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
      simpa only [one_div] using
        (Real.le_rpow_inv_iff_of_pos
          (by positivity) (by positivity) hkreal).mpr
            (by simpa [Real.rpow_natCast] using hramsey)
