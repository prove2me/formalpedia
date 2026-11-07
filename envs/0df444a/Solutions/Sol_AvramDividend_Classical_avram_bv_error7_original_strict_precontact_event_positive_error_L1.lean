-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_strict_precontact_event_positive_error_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:40:54.24558+00:00
-- url     : https://prove2.me/submissions/3a6a696d-3953-4324-b06c-a04c03cd18af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_event_positive_error_L1_of_Borel_jet
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_stopped_strict_precontact_grid_geometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original strictly precontact stopped-grid positive error tends to zero
in expectation on exhausting interior events, using genuine BV source-mass
domination off those events and excluding the single contact cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hwMeas : Measurable w)
    (hDerivMeas : Measurable (deriv w))
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b L : ℕ → ℝ)
    (hBand : ∀ n, Set.Icc (a n) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hL : ∀ n, 0 ≤ L n)
    (hLip : ∀ n, ∀ y ∈ Set.Icc (a n) (b n),
      ∀ z ∈ Set.Icc (a n) (b n),
        |w z - w y| ≤ L n * |z - y|)
    (hDeriv : ∀ n, ∀ y ∈ Set.Icc (a n) (b n),
      |deriv w y| ≤ L n)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (k : ℕ → Ω → ℕ) (hk : ∀ m, Measurable (k m))
    (hBound : ∀ m ω, k m ω ≤ N m)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1)))
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n)
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m ω - 1),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ n, ∀ᵐ ω ∂P, ω ∈ s n →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m (i + 1)) - Y (u m i)
       (∀ m i, i < k m ω - 1 →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc (a n) (b n)) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω - 1 → |c m i| < δ)))
    (K : ℝ) (hK : 0 ≤ K)
    (hOutside : ∀ n m, ∀ᵐ ω ∂P, ω ∉ s n →
      max (Err m ω) 0 ≤
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hkStrict : ∀ m, Measurable (fun ω => k m ω - 1) := by
    intro m
    fun_prop
  have hBoundStrict : ∀ m ω, k m ω - 1 ≤ N m := by
    intro m ω
    exact (Nat.sub_le _ _).trans (hBound m ω)
  have hGridStrict :=
    avram_bv_error7_original_stopped_strict_precontact_grid_geometry u k T hGrid
  exact avram_bv_error7_original_random_stopped_event_positive_error_L1_of_Borel_jet
    X hX hBV x C D hD w hwMeas hDerivMeas hwC1 hOpen
    a b L hBand hL hLip hDeriv q hq T hT
    u N (fun m ω => k m ω - 1) hkStrict hBoundStrict hGridStrict
    s hs hExhaust Err hSource hPath K hK hOutside
