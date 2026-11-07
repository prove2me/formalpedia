-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_random_stopped_final_contact_error_AE_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:32:37.229277+00:00
-- url     : https://prove2.me/submissions/0e03a7d3-6a61-4c6b-834b-4ba9e67cd7a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The exact original random-stopped final contact Taylor source, obtained
as full physical sum minus strict precontact sum, is a.e. measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hwMeas : Measurable w)
    (hDerivMeas : Measurable (deriv w)) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (k : ℕ → Ω → ℕ) (hk : ∀ m, Measurable (k m))
    (hBound : ∀ m ω, k m ω ≤ N m)
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
    ∀ m, AEStronglyMeasurable
      (fun ω => ErrFull m ω - ErrStrict m ω) P := by
  have hkStrict : ∀ m, Measurable (fun ω => k m ω - 1) := by
    intro m
    fun_prop
  have hBoundStrict : ∀ m ω, k m ω - 1 ≤ N m := by
    intro m ω
    exact (Nat.sub_le _ _).trans (hBound m ω)
  have hFullMeas :=
    avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
      X hX hBV x C D hD w hwMeas hDerivMeas q
      u N k hk hBound ErrFull hFull
  have hStrictMeas :=
    avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
      X hX hBV x C D hD w hwMeas hDerivMeas q
      u N (fun m ω => k m ω - 1) hkStrict hBoundStrict ErrStrict hStrict
  intro m
  exact (hFullMeas m).sub (hStrictMeas m)
