-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_variable_endpoint_C1_mesh_error_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:47:17.155149+00:00
-- url     : https://prove2.me/submissions/e3ddedfb-2797-4ced-b1bf-cd6342b190a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The exact original X/D C1 Taylor error vanishes almost surely on
sample-dependent physical prefixes ending at any time at most T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → Ω → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m ω 0 = 0 ∧ u m ω (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m ω i ≤ u m ω (i + 1)))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℝ := fun i => Y (u m ω (i + 1)) - Y (u m ω i)
       ∑ i ∈ Finset.range (k m ω),
         Real.exp (-(q * (u m ω i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m ω (i + 1)) - Y (u m ω i)
       (∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ))) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by
  filter_upwards
    [avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
      X hBV T, hPath] with ω hMass hPathω
  dsimp at hPathω
  obtain ⟨hCells, hRefine⟩ := hPathω
  let H : ℝ := |X.drift| * (T : ℝ) +
    |(T : ℝ) * X.drift - X.X T ω|
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    positivity
  have hHpos : 0 < H + 1 := by linarith
  apply (Metric.tendsto_atTop).2
  intro η hη
  have hε : 0 < η / (H + 1) := div_pos hη hHpos
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
      X x C D hD w hwC1 hOpen a b hBand q hq
      (η / (H + 1)) hε
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 (hRefine δ hδ)
  refine ⟨N, ?_⟩
  intro m hm
  obtain ⟨h0, hEnd, hMono⟩ := hGrid m ω
  have hBound :=
    hMass (u m ω) (k m ω) h0 hEnd hMono
  have hCell := hTaylor ω (u m ω) (k m ω)
    (hCells m) (hN m hm)
  have hErr : |Err m ω| ≤ (η / (H + 1)) * H := by
    rw [hSource m ω]
    exact le_trans hCell
      (mul_le_mul_of_nonneg_left hBound (le_of_lt hε))
  have hRatio : H / (H + 1) < 1 := by
    apply (div_lt_one hHpos).2
    linarith
  have hSmall : (η / (H + 1)) * H < η := by
    calc
      (η / (H + 1)) * H = η * (H / (H + 1)) := by ring
      _ < η * 1 := mul_lt_mul_of_pos_left hRatio hη
      _ = η := by ring
  simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt hErr hSmall
