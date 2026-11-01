-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_finite_horizon_actual_right_payment_jumps_summable_on_atom_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:01:16.696988+00:00
-- url     : https://prove2.me/submissions/2b4b403e-67bd-4cd9-aa10-ccccad000024

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Real summability of actual dividend singleton masses on a stopped
finite window transfers to the chronological right-payment sizes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (A : Set ℝ)
    (hAwindow : ∀ s : A, (0 : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (T : ℝ))
    (hMass : Summable (fun s : A => (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(s : ℝ)}).toReal)) :
    Summable (fun s : A => rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  have hRealMass : Summable (fun s : A => (μ {(s : ℝ)}).toReal) := by
    exact hMass
  have hEq (s : A) : (μ {(s : ℝ)}).toReal = rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω := by
    have hCoe : (((s : ℝ).toNNReal : ℝ≥0) : ℝ) = (s : ℝ) :=
      Real.coe_toNNReal (s : ℝ) (hAwindow s).1
    have hmem : (s : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
      hAwindow s
    have hDeltaNonneg : 0 ≤ rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω := by
      exact sub_nonneg.mpr
        (dividendStrategy_le_rightLimit D hD ω ((s : ℝ).toNNReal))
    have hAtom :
        μ {(s : ℝ)} = ENNReal.ofReal (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) := by
      calc
        μ {(s : ℝ)} = (dividendMeasure D ω) {(s : ℝ)} := by
          simp [μ, hmem]
        _ = ENNReal.ofReal (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) := by
          simpa only [hCoe] using
            (dividendMeasure_singleton_eq_rightLimit_sub
              D hD ω ((s : ℝ).toNNReal))
    rw [hAtom, ENNReal.toReal_ofReal hDeltaNonneg]
  have hFunctions :
      (fun s : A => (μ {(s : ℝ)}).toReal) =
        (fun s : A => rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) := by
    funext s
    exact hEq s
  rw [hFunctions] at hRealMass
  exact hRealMass
