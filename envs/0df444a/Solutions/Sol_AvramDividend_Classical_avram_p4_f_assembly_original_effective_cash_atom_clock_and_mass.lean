-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_effective_cash_atom_clock_and_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:20:27.591272+00:00
-- url     : https://prove2.me/submissions/9160df63-610d-4ee8-bd82-7f145cd0c14c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Effective original Cash atoms have valid physical clocks and exact source masses. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hRight : ∀ t : ℝ≥0, t ≤ T →
      μatom {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω))
    (A : Set ℝ) :
    ∀ a : {t : ℝ | t ∈ A ∧ μatom {t} ≠ 0},
      0 ≤ a.1 ∧ Real.toNNReal a.1 ≤ T ∧
        μatom {a.1} = ENNReal.ofReal
          (rightLimit D (Real.toNNReal a.1) ω -
            D (Real.toNNReal a.1) ω) := by
  intro a
  have hloc := avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
    D ω T μatom μdiffuse hsplit A ⟨a.1, a.2.1⟩ a.2.2
  have hcast : (Real.toNNReal a.1 : ℝ) = a.1 := by
    simpa [hloc.1] using (Real.coe_toNNReal a.1)
  have hclock : Real.toNNReal a.1 ≤ T := by
    exact_mod_cast (show (Real.toNNReal a.1 : ℝ) ≤ (T : ℝ) by
      simpa [hcast] using hloc.2)
  have hAtom := hRight (Real.toNNReal a.1) hclock
  exact ⟨hloc.1, hclock, by simpa [hcast] using hAtom⟩
