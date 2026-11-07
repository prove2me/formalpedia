-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_full_stopped_Taylor_positive_error_L1_of_exact_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:51:30.523195+00:00
-- url     : https://prove2.me/submissions/a95fbd07-8090-4d62-b4f9-b043d50a3b32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_final_contact_Taylor_exact_difference
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_strict_contact_positive_error_L1_absorption
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The full genuine original stopped-grid Taylor source has vanishing positive expectation if its strict and contact components do, with the exact contact identity proved from the original physical sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (ErrFull ErrStrict ErrContact : ℕ → Ω → ℝ)
    (hFull : ∀ m ω, ErrFull m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       let g : ℕ → ℝ := fun i =>
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)
       ∑ i ∈ Finset.range (k m ω), g i))
    (hStrict : ∀ m ω, ErrStrict m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       let g : ℕ → ℝ := fun i =>
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)
       ∑ i ∈ Finset.range (k m ω - 1), g i))
    (hContact : ∀ m ω, ErrContact m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       let g : ℕ → ℝ := fun i =>
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)
       if k m ω = 0 then 0 else g (k m ω - 1)))
    (hFullMeas : ∀ m, AEStronglyMeasurable (fun ω => max (ErrFull m ω) 0) P)
    (hStrictInt : ∀ m, Integrable (fun ω => max (ErrStrict m ω) 0) P)
    (hContactInt : ∀ m, Integrable (fun ω => max (ErrContact m ω) 0) P)
    (hStrictMean : Tendsto (fun m => ∫ ω, max (ErrStrict m ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hContactMean : Tendsto (fun m => ∫ ω, max (ErrContact m ω) 0 ∂P) atTop (nhds (0 : ℝ))) :
    (∀ m, Integrable (fun ω => max (ErrFull m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (ErrFull m ω) 0 ∂P) atTop (nhds (0 : ℝ))
 := by
  have hDiff :=
    avram_bv_error7_original_random_stopped_final_contact_Taylor_exact_difference
      X x D w q u k ErrFull ErrStrict hFull hStrict
  have hSplit : ∀ m ω, ErrFull m ω = ErrStrict m ω + ErrContact m ω := by
    intro m ω
    have hd := hDiff m ω
    rw [←hContact m ω] at hd
    linarith
  exact avram_bv_error7_strict_contact_positive_error_L1_absorption
    P ErrStrict ErrContact ErrFull hSplit hFullMeas hStrictInt
    hContactInt hStrictMean hContactMean

