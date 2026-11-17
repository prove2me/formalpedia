-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_signed_capkink_two_positive_errors_L1_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:50:57.514722+00:00
-- url     : https://prove2.me/submissions/71e24cf7-6513-452c-bb4a-b5d89c1f6bf4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (K : Ω → ℝ) (M E C T : ℕ → Ω → ℝ)
    (hKI : Integrable K (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hEI : ∀ m, Integrable (E m) (P.restrict A))
    (hCI : ∀ m, Integrable (C m) (P.restrict A))
    (hKink : ∀ m, ∀ᵐ ω ∂(P.restrict A), 0 ≤ T m ω)
    (hLedger : ∀ m, ∀ᵐ ω ∂(P.restrict A),
       K ω - M m ω ≤ E m ω + C m ω - T m ω)
    (hEt : Tendsto (fun m => ∫ ω in A, max (E m ω) 0 ∂P)
       atTop (nhds (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω in A, max (C m ω) 0 ∂P)
       atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A, max (K ω - M m ω) 0 ∂P)
       atTop (nhds (0 : ℝ)) := by
  have hI (m : ℕ) :
      Integrable (fun ω => max (K ω - M m ω) 0) (P.restrict A) :=
    (hKI.sub (hMI m)).sup (integrable_zero Ω ℝ (P.restrict A))
  have hE (m : ℕ) :
      Integrable (fun ω => max (E m ω) 0) (P.restrict A) :=
    (hEI m).sup (integrable_zero Ω ℝ (P.restrict A))
  have hC (m : ℕ) :
      Integrable (fun ω => max (C m ω) 0) (P.restrict A) :=
    (hCI m).sup (integrable_zero Ω ℝ (P.restrict A))
  have hBound (m : ℕ) :
      (∫ ω in A, max (K ω - M m ω) 0 ∂P) ≤
      (∫ ω in A, max (E m ω) 0 ∂P) +
      (∫ ω in A, max (C m ω) 0 ∂P) := by
    calc
      _ ≤ ∫ ω in A, max (E m ω) 0 + max (C m ω) 0 ∂P := by
        apply integral_mono_ae (hI m) ((hE m).add (hC m))
        filter_upwards [hLedger m, hKink m] with ω hledger hkink
        have he := le_max_left (E m ω) 0
        have hc := le_max_left (C m ω) 0
        have he0 := le_max_right (E m ω) 0
        have hc0 := le_max_right (C m ω) 0
        change max (K ω - M m ω) 0 ≤
          max (E m ω) 0 + max (C m ω) 0
        apply max_le
        · linarith
        · linarith
      _ = _ := integral_add (hE m) (hC m)
  have hLower (m : ℕ) :
      0 ≤ ∫ ω in A, max (K ω - M m ω) 0 ∂P :=
    integral_nonneg (fun ω => le_max_right _ _)
  have hSum : Tendsto (fun m =>
      (∫ ω in A, max (E m ω) 0 ∂P) +
      (∫ ω in A, max (C m ω) 0 ∂P))
      atTop (nhds (0 : ℝ)) := by
    simpa using hEt.add hCt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hSum hLower hBound
