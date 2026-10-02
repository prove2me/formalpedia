-- Prove2me | solution 1 for ErlerGross.B3_cubic_reciprocal_series_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:32:26.293281+00:00
-- url     : https://prove2.me/submissions/08d32db0-e4b0-4219-89f6-988aae06ddeb

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_B3_series_digamma
import Theorems.Thm_ErlerGross_B3_digamma_values

open Real Filter Topology MeasureTheory

theorem solution :
    HasSum (fun n : Nat => 1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2))))
      (Real.log (27 / 16)) := by
  have hC := ErlerGross.B3_series_digamma
  have hR := Complex.reCLM.hasSum hC
  have hB3 : HasSum (fun n : Nat => ErlerGross.b3Term (n + 1))
      (-Real.log (27 / 16) / 2) := by
    have hr : HasSum (fun n : Nat => ErlerGross.b3Term (n + 1))
        (Complex.reCLM
          (Complex.digamma ((2 : Complex) / 3) / 2 + Complex.digamma ((1 : Complex) / 3) / 2 -
            Complex.digamma ((1 : Complex) / 2))) := by
      convert hR using 1 <;> simp [Complex.reCLM_apply]
    rw [ErlerGross.B3_digamma_values] at hr
    simpa [Complex.reCLM_apply] using hr
  have hscaled := hB3.mul_left (-2)
  have hterm : forall n : Nat,
      ErlerGross.b3Term (n + 1) = (-1 / 2) *
        (1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2)))) := by
    intro n
    rw [ErlerGross.b3Term]
    push_cast
    have h1 : (0 : Real) < 2 * (n : Real) + 1 := by positivity
    have h2 : (0 : Real) < 3 * (n : Real) + 1 := by positivity
    have h3 : (0 : Real) < 3 * (n : Real) + 2 := by positivity
    have h4 : (0 : Real) < 1 + (n : Real) * 2 := by positivity
    have h5 : (0 : Real) < 2 + (n : Real) * 3 := by positivity
    have h6 : (0 : Real) < 2 + (n : Real) * 6 := by positivity
    have h7 : (0 : Real) < 2 * ((n : Real) + 1) - 1 := by
      have hn : (0 : Real) <= (n : Real) := by positivity
      nlinarith
    have h8 : (0 : Real) < ((n : Real) + 1) * 3 - 1 := by
      have hn : (0 : Real) <= (n : Real) := by positivity
      nlinarith
    have h9 : (0 : Real) < 2 * ((n : Real) + 1) * 3 - 4 := by
      have hn : (0 : Real) <= (n : Real) := by positivity
      nlinarith
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3, ne_of_gt h4, ne_of_gt h5,
      ne_of_gt h6, ne_of_gt h7, ne_of_gt h8, ne_of_gt h9]
    ring
  have hterm' : forall n : Nat,
      (-2) * ErlerGross.b3Term (n + 1) =
        1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2))) := by
    intro n
    rw [hterm n]
    ring
  have hs := hscaled.congr_fun (fun n => (hterm' n).symm)
  rw [show (-2 : Real) * (-Real.log (27 / 16) / 2) = Real.log (27 / 16) by ring] at hs
  exact hs