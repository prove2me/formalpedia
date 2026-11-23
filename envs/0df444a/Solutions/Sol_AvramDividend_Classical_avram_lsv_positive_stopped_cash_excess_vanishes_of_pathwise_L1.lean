-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_positive_stopped_cash_excess_vanishes_of_pathwise_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:24:38.071023+00:00
-- url     : https://prove2.me/submissions/3b582b10-38db-4f5a-9e02-3d781f8095cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (g Z : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hI : ∀ m, Integrable (fun ω => max (g ω - M m ω) 0) (P.restrict A))
    (hDI : ∀ m, Integrable (fun ω => |Z ω - M m ω|) (P.restrict A))
    (hL : Tendsto (fun m => ∫ ω in A, |Z ω - M m ω| ∂P)
      atTop (nhds (0 : ℝ)))
    (hPath : ∀ᵐ ω ∂(P.restrict A), g ω ≤ Z ω) :
    Tendsto (fun m => ∫ ω in A, max (g ω - M m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hUpper (m : ℕ) :
      (∫ ω in A, max (g ω - M m ω) 0 ∂P) ≤
        ∫ ω in A, |Z ω - M m ω| ∂P := by
    apply integral_mono_ae (hI m) (hDI m)
    filter_upwards [hPath] with ω hω
    apply max_le
    · exact (sub_le_sub_right hω (M m ω)).trans (le_abs_self _)
    · exact abs_nonneg _
  have hLower (m : ℕ) :
      (0 : ℝ) ≤ ∫ ω in A, max (g ω - M m ω) 0 ∂P := by
    apply integral_nonneg
    intro ω
    exact le_max_right _ _
  exact squeeze_zero hLower hUpper hL
