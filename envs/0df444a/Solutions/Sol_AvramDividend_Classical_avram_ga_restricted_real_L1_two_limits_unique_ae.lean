-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_restricted_real_L1_two_limits_unique_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:51:17.022983+00:00
-- url     : https://prove2.me/submissions/37cc73cb-cc84-4016-a16a-1f6a6c6101f8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (N N0 : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hNI : Integrable N (P.restrict A))
    (hN0I : Integrable N0 (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
       atTop (nhds (0 : ℝ)))
    (hL10 : Tendsto (fun m => ∫ ω in A, |N0 ω - M m ω| ∂P)
       atTop (nhds (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), N ω = N0 ω := by
  have hDI (m : ℕ) : Integrable (fun ω => |N ω - M m ω|) (P.restrict A) :=
    (hNI.sub (hMI m)).abs
  have hD0I (m : ℕ) : Integrable (fun ω => |N0 ω - M m ω|) (P.restrict A) :=
    (hN0I.sub (hMI m)).abs
  have hI : Integrable (fun ω => |N ω - N0 ω|) (P.restrict A) :=
    (hNI.sub hN0I).abs
  have hBound (m : ℕ) : (∫ ω in A, |N ω - N0 ω| ∂P) ≤
      (∫ ω in A, |N ω - M m ω| ∂P) +
      (∫ ω in A, |N0 ω - M m ω| ∂P) := by
    calc
      _ ≤ ∫ ω in A, |N ω - M m ω| + |N0 ω - M m ω| ∂P := by
        apply integral_mono_ae hI ((hDI m).add (hD0I m))
        exact Filter.Eventually.of_forall (fun ω => by
          calc
            |N ω - N0 ω| ≤ |N ω - M m ω| + |M m ω - N0 ω| :=
              abs_sub_le _ _ _
            _ = _ := congrArg (fun z : ℝ => |N ω - M m ω| + z)
              (abs_sub_comm (M m ω) (N0 ω)))
      _ = _ := integral_add (hDI m) (hD0I m)
  have hZero : (∫ ω in A, |N ω - N0 ω| ∂P) = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto tendsto_const_nhds
        (by simpa only [add_zero] using hL1.add hL10)
        (Filter.Eventually.of_forall hBound)
    · exact integral_nonneg (fun ω => abs_nonneg _)
  have hAE : ∀ᵐ ω ∂(P.restrict A), |N ω - N0 ω| = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => abs_nonneg _)) hI).mp hZero
  filter_upwards [hAE] with ω hω
  exact sub_eq_zero.mp (abs_eq_zero.mp hω)
