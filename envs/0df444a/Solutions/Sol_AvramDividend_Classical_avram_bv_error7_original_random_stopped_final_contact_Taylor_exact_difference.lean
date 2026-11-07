-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_random_stopped_final_contact_Taylor_exact_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:32:56.586214+00:00
-- url     : https://prove2.me/submissions/45aa26eb-4fe8-4803-8882-d4b5be67600f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual original BV final stopped physical contact Taylor cell is
exactly the difference between the full source and strict precontact source,
with the zero-clock case treated without an artificial terminal atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (ErrFull ErrStrict : ℕ → Ω → ℝ)
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
       ∑ i ∈ Finset.range (k m ω - 1), g i)) :
    ∀ m ω, ErrFull m ω - ErrStrict m ω =
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
       if k m ω = 0 then 0 else g (k m ω - 1)) := by
  intro m ω
  rw [hFull m ω, hStrict m ω]
  dsimp
  let J : ℝ≥0 → ℝ := fun t =>
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
  change (∑ i ∈ Finset.range (k m ω), g i) -
      (∑ i ∈ Finset.range (k m ω - 1), g i) =
      if k m ω = 0 then 0 else g (k m ω - 1)
  by_cases hk : k m ω = 0
  · simp [hk]
  · have hN : k m ω - 1 + 1 = k m ω := by omega
    have hSum :
        (∑ i ∈ Finset.range (k m ω), g i) =
          (∑ i ∈ Finset.range (k m ω - 1), g i) +
            g (k m ω - 1) := by
      simpa only [hN] using
        (Finset.sum_range_succ g (k m ω - 1))
    rw [hSum, if_neg hk]
    ring
