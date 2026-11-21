-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_transfer_stopped_pathwise_L1_positive_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:16:40.440727+00:00
-- url     : https://prove2.me/submissions/84f46284-2325-4690-bdab-3767c82de355

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Set Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (G N : Ω → ℝ) (M B : ℕ → Ω → ℝ)
    (hG : ∀ᵐ ω ∂(P.restrict A), G ω ≤ N ω)
    (hInt : ∀ m, Integrable
      (fun ω => max (G ω - M m ω - B m ω) (0 : ℝ)) (P.restrict A))
    (hUpperI : ∀ m, Integrable
      (fun ω => |N ω - M m ω| + |B m ω|) (P.restrict A))
    (hUpperLim : Tendsto
      (fun m => ∫ ω in A, |N ω - M m ω| + |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A,
      max (G ω - M m ω - B m ω) (0 : ℝ) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  have hPoint (m : ℕ) : ∀ᵐ ω ∂(P.restrict A),
      max (G ω - M m ω - B m ω) (0 : ℝ) ≤
        |N ω - M m ω| + |B m ω| := by
    filter_upwards [hG] with ω hω
    have h1 : G ω - M m ω - B m ω ≤
        |N ω - M m ω| + |B m ω| := by
      linarith [le_abs_self (N ω - M m ω), neg_le_abs (B m ω)]
    exact max_le h1 (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hBound (m : ℕ) :
      0 ≤ (∫ ω in A, max (G ω - M m ω - B m ω) (0 : ℝ) ∂P) ∧
      (∫ ω in A, max (G ω - M m ω - B m ω) (0 : ℝ) ∂P) ≤
      ∫ ω in A, |N ω - M m ω| + |B m ω| ∂P := by
    constructor
    · exact integral_nonneg_of_ae (Filter.Eventually.of_forall
        (fun ω => le_max_right _ _))
    · exact integral_mono_ae (hInt m) (hUpperI m) (hPoint m)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hUpperLim
  · exact Filter.Eventually.of_forall (fun m => (hBound m).1)
  · exact Filter.Eventually.of_forall (fun m => (hBound m).2)
