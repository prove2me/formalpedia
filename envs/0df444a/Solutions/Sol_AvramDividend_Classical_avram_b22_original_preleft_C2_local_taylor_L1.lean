-- Prove2me | solution 1 for AvramDividend.Classical.avram_b22_original_preleft_C2_local_taylor_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:41:07.465836+00:00
-- url     : https://prove2.me/submissions/bfc77392-2c2f-4cbe-9539-0be9a71d513e

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Convert the original physical pre-left compact Taylor modulus to a restricted L1 energy estimate. -/
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
        IntegrableOn (fun ω => |R ω|) A P →
        IntegrableOn Q A P →
        (∫ ω in A, |R ω| ∂P) ≤
          ε * (∫ ω in A, Q ω ∂P) := by
  classical
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
      X x D hD C w hw a b ha hab hbcap ε hε
  refine ⟨δ, hδ, ?_⟩
  intro A S s t
  dsimp only
  intro hBand hRI hQI
  have hIntegral := integral_mono_ae hRI (hQI.const_mul ε) (by
    filter_upwards [hBand] with ω hω
    exact hTaylor ω S s t (by
      intro i hi
      exact hω i hi))
  simpa only [integral_const_mul] using hIntegral
