-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_strict_contact_positive_error_L1_absorption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:46:39.944527+00:00
-- url     : https://prove2.me/submissions/7e3c6987-6bab-4590-b632-19c65d3e7951

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A stopped-grid Taylor error split into strict interior and one contact
cell has vanishing positive expectation if each positive part is L1-small.
The analytic combination does not use a signed dividend prebudget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ErrStrict ErrContact ErrFull : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, ErrFull m ω = ErrStrict m ω + ErrContact m ω)
    (hFullMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max (ErrFull m ω) 0) P)
    (hStrictInt : ∀ m, Integrable (fun ω => max (ErrStrict m ω) 0) P)
    (hContactInt : ∀ m, Integrable (fun ω => max (ErrContact m ω) 0) P)
    (hStrictMean : Tendsto (fun m => ∫ ω,
      max (ErrStrict m ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hContactMean : Tendsto (fun m => ∫ ω,
      max (ErrContact m ω) 0 ∂P) atTop (nhds (0 : ℝ))) :
    (∀ m, Integrable (fun ω => max (ErrFull m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (ErrFull m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hPoint (a b : ℝ) : max (a + b) 0 ≤ max a 0 + max b 0 := by
    apply max_le
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hFullInt (m : ℕ) :
      Integrable (fun ω => max (ErrFull m ω) 0) P := by
    have hSum := (hStrictInt m).add (hContactInt m)
    apply hSum.mono' (hFullMeas m)
    filter_upwards [] with ω
    rw [hSplit m ω]
    have hp : 0 ≤ max (ErrStrict m ω + ErrContact m ω) 0 :=
      le_max_right _ _
    calc
      ‖max (ErrStrict m ω + ErrContact m ω) 0‖ =
          max (ErrStrict m ω + ErrContact m ω) 0 := Real.norm_of_nonneg hp
      _ ≤ max (ErrStrict m ω) 0 + max (ErrContact m ω) 0 :=
        hPoint _ _
  refine ⟨hFullInt, ?_⟩
  have hBound (m : ℕ) :
      0 ≤ (∫ ω, max (ErrFull m ω) 0 ∂P) ∧
      (∫ ω, max (ErrFull m ω) 0 ∂P) ≤
        (∫ ω, max (ErrStrict m ω) 0 ∂P) +
        (∫ ω, max (ErrContact m ω) 0 ∂P) := by
    constructor
    · exact integral_nonneg (fun ω => le_max_right _ _)
    · calc
        _ ≤ ∫ ω, max (ErrStrict m ω) 0 +
            max (ErrContact m ω) 0 ∂P := by
              apply integral_mono (hFullInt m)
                ((hStrictInt m).add (hContactInt m))
              intro ω
              change max (ErrFull m ω) 0 ≤
                max (ErrStrict m ω) 0 + max (ErrContact m ω) 0
              rw [hSplit m ω]
              exact hPoint (ErrStrict m ω) (ErrContact m ω)
        _ = (∫ ω, max (ErrStrict m ω) 0 ∂P) +
            (∫ ω, max (ErrContact m ω) 0 ∂P) :=
          integral_add (hStrictInt m) (hContactInt m)
  have hSumMean := hStrictMean.add hContactMean
  apply (Metric.tendsto_atTop).2
  intro ε hε
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop).1 (by simpa using hSumMean) ε hε
  refine ⟨N, ?_⟩
  intro m hm
  obtain ⟨hn, hu⟩ := hBound m
  have hsum := hN m hm
  simp only [Real.dist_eq, sub_zero] at hsum ⊢
  rw [abs_of_nonneg hn]
  exact lt_of_le_of_lt hu (lt_of_le_of_lt (le_abs_self _) hsum)
