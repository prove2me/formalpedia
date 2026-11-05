-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_integrable_diagonals_of_L2_Linfty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:38:11.16176+00:00
-- url     : https://prove2.me/submissions/50a2b4ab-7f61-4cc1-84d9-f3d2ebea3455

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Source-independent analytic L²/L∞ integrability for intrinsic count diagonals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (J H : Ω → ℝ) (hJ : MemLp J 2 P) (hH : MemLp H ⊤ P) :
    Integrable (fun ω => (J ω) ^ 2) P ∧
    Integrable (fun ω => (H ω) ^ 2) P ∧
    Integrable (fun ω => (H ω) ^ 2 * (J ω) ^ 2) P := by
  constructor
  · exact hJ.integrable_sq
  constructor
  · exact (hH.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ⊤)).integrable_sq
  have hProduct : MemLp (fun ω => H ω * J ω) 2 P := by
    have hMul : MemLp (H * J) 2 P := hJ.mul hH
    convert hMul using 1
    funext ω
    simp only [Pi.mul_apply]
  convert hProduct.integrable_sq using 1
  funext ω
  ring
