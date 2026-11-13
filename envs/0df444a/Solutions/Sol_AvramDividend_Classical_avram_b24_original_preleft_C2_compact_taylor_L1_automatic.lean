-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_preleft_C2_compact_taylor_L1_automatic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:42:01.591065+00:00
-- url     : https://prove2.me/submissions/8b5e80e0-6f07-468e-aa32-72a9a51371cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
import Theorems.Thm_AvramDividend_Classical_avram_b23_original_compact_preleft_mesh_square_energy_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Compact original stopped physical Taylor errors are automatically locally L1 given measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (A : Set Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0),
        let z : Ω → ℕ → ℝ := fun ω i =>
          Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i)
        let g : Ω → ℕ → ℝ := fun ω i =>
          X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
        let R : Ω → ℝ := fun ω => ∑ i ∈ S,
          (w (z ω i + g ω i) -
            taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
              (z ω i) (z ω i + g ω i) -
            (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
        let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
        (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
          z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b ∧
          z ω i ≠ z ω i + g ω i ∧
          dist (z ω i + g ω i) (z ω i) < δ) →
        AEStronglyMeasurable Q (P.restrict A) →
        AEStronglyMeasurable (fun ω => |R ω|) (P.restrict A) →
        IntegrableOn (fun ω => |R ω|) A P ∧
        (∫ ω in A, |R ω| ∂P) ≤
          ε * (∫ ω in A, Q ω ∂P) := by
  classical
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
      X x D hD C w hw a b ha hab hbcap ε hε
  refine ⟨δ, hδ, ?_⟩
  intro A S s t
  dsimp only
  intro hBand hQMeas hRMeas
  let z : Ω → ℕ → ℝ := fun ω i =>
    Function.leftLim (fun u : ℝ≥0 =>
      x + X.X u ω - rightLimit D u ω) (s i)
  let g : Ω → ℕ → ℝ := fun ω i =>
    X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
  let R : Ω → ℝ := fun ω => ∑ i ∈ S,
    (w (z ω i + g ω i) -
      taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
        (z ω i) (z ω i + g ω i) -
      (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
  let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
  have hBandWeak : ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
      z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b := by
    filter_upwards [hBand] with ω hω i hi
    exact ⟨(hω i hi).1, (hω i hi).2.1⟩
  have hQint : IntegrableOn Q A P :=
    avram_b23_original_compact_preleft_mesh_square_energy_L1
      X x D a b hab A S s t hBandWeak hQMeas
  have hMod : ∀ᵐ ω ∂(P.restrict A),
      |R ω| ≤ ε * Q ω := by
    filter_upwards [hBand] with ω hω
    exact hTaylor ω S s t (by
      intro i hi
      exact hω i hi)
  have hRint : IntegrableOn (fun ω => |R ω|) A P :=
    Integrable.mono' (hQint.const_mul ε) hRMeas (by
      filter_upwards [hMod] with ω hω
      simpa [Real.norm_eq_abs] using hω)
  refine ⟨hRint, ?_⟩
  have hI := integral_mono_ae hRint (hQint.const_mul ε) hMod
  simpa only [integral_const_mul] using hI
