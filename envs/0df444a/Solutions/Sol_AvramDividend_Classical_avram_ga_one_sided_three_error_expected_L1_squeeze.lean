-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_one_sided_three_error_expected_L1_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:36:16.487873+00:00
-- url     : https://prove2.me/submissions/da3dc224-2037-4951-a0ee-6f08dbe9e022

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (F T B C : ℕ → Ω → ℝ)
    (hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) (P.restrict A))
    (hTI : ∀ m, Integrable (fun ω => max (T m ω) 0) (P.restrict A))
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) (P.restrict A))
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) (P.restrict A))
    (hBound : ∀ m, ∀ᵐ ω ∂(P.restrict A),
      max (F m ω) 0 ≤ max (T m ω) 0 + |B m ω| + max (C m ω) 0)
    (hTt : Tendsto (fun m => ∫ ω in A, max (T m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω in A, |B m ω| ∂P)
      atTop (nhds (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω in A, max (C m ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A, max (F m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hUpper (m : ℕ) :
      (∫ ω in A, max (F m ω) 0 ∂P) ≤
      (∫ ω in A, max (T m ω) 0 ∂P) +
      (∫ ω in A, |B m ω| ∂P) +
      (∫ ω in A, max (C m ω) 0 ∂P) := by
    calc
      _ ≤ ∫ ω in A,
          (max (T m ω) 0 + |B m ω|) + max (C m ω) 0 ∂P :=
        integral_mono_ae (hFI m) (((hTI m).add (hBI m)).add (hCI m))
          (hBound m)
      _ = _ := by
        have hOne : (∫ ω in A,
          (max (T m ω) 0 + |B m ω|) + max (C m ω) 0 ∂P) =
          (∫ ω in A, max (T m ω) 0 + |B m ω| ∂P) +
          (∫ ω in A, max (C m ω) 0 ∂P) :=
          integral_add ((hTI m).add (hBI m)) (hCI m)
        have hTwo : (∫ ω in A, max (T m ω) 0 + |B m ω| ∂P) =
          (∫ ω in A, max (T m ω) 0 ∂P) +
          (∫ ω in A, |B m ω| ∂P) :=
          integral_add (hTI m) (hBI m)
        calc
          _ = (∫ ω in A, max (T m ω) 0 + |B m ω| ∂P) +
              (∫ ω in A, max (C m ω) 0 ∂P) := hOne
          _ = _ := congrArg (fun r => r + ∫ ω in A, max (C m ω) 0 ∂P) hTwo
  have hLower (m : ℕ) :
      0 ≤ ∫ ω in A, max (F m ω) 0 ∂P :=
    integral_nonneg (fun ω => le_max_right _ _)
  have hSum : Tendsto (fun m =>
      (∫ ω in A, max (T m ω) 0 ∂P) +
      (∫ ω in A, |B m ω| ∂P) +
      (∫ ω in A, max (C m ω) 0 ∂P))
      atTop (nhds (0 : ℝ)) := by
    simpa only [add_zero] using (hTt.add hBt).add hCt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hSum hLower hUpper
