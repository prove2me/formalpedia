-- Prove2me | solution 1 for AvramDividend.Classical.avram_b28_original_random_clipped_C2_taylor_L1_automatic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:57:13.234391+00:00
-- url     : https://prove2.me/submissions/65a6f5ce-d6e2-423a-8492-512f7b459f74

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_compact_gaussian_finite_mesh_remainder
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_random_stopped_compact_mesh_energy_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original random stopped and final clipped cell physical C2 Taylor error is locally L1. -/
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
      ∀ (A : Set Ω) (S : Finset ℕ)
        (s t : ℕ → Ω → ℝ≥0),
        let z : Ω → ℕ → ℝ := fun ω i =>
          Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u ω - rightLimit D u ω) (s i ω)
        let g : Ω → ℕ → ℝ := fun ω i =>
          X.X (t i ω) ω - X.X (s i ω) ω -
            ((t i ω - s i ω) : ℝ) * X.c
        let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
        let R : Ω → ℝ := fun ω => ∑ i ∈ S,
          (w (z ω i + g ω i) -
            taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
              (z ω i) (z ω i + g ω i) -
            (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
        (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
          (fun ω => (s i ω : WithTop ℝ≥0))) →
        (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
          (fun ω => (t i ω : WithTop ℝ≥0))) →
        (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
          z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b ∧
          z ω i ≠ z ω i + g ω i ∧
          dist (z ω i + g ω i) (z ω i) < δ) →
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
  intro hs ht hBand hRMeas
  let z : Ω → ℕ → ℝ := fun ω i =>
    Function.leftLim (fun u : ℝ≥0 =>
      x + X.X u ω - rightLimit D u ω) (s i ω)
  let g : Ω → ℕ → ℝ := fun ω i =>
    X.X (t i ω) ω - X.X (s i ω) ω -
      ((t i ω - s i ω) : ℝ) * X.c
  let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
  let R : Ω → ℝ := fun ω => ∑ i ∈ S,
    (w (z ω i + g ω i) -
      taylorWithinEval w 1 (Set.uIcc (z ω i) (z ω i + g ω i))
        (z ω i) (z ω i + g ω i) -
      (iteratedDeriv 2 w (z ω i) * (g ω i) ^ 2) / 2)
  have hBandWeak : ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
      z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b := by
    filter_upwards [hBand] with ω hω i hi
    exact ⟨(hω i hi).1, (hω i hi).2.1⟩
  have hQint : IntegrableOn Q A P :=
    avram_b27_original_random_stopped_compact_mesh_energy_L1
      X x D a b hab A S s t hs ht hBandWeak
  have hMod : ∀ᵐ ω ∂(P.restrict A),
      |R ω| ≤ ε * Q ω := by
    filter_upwards [hBand] with ω hω
    exact hTaylor ω S (fun i => s i ω) (fun i => t i ω) (by
      intro i hi
      exact hω i hi)
  have hRint : IntegrableOn (fun ω => |R ω|) A P :=
    Integrable.mono' (hQint.const_mul ε) hRMeas (by
      filter_upwards [hMod] with ω hω
      simpa [Real.norm_eq_abs] using hω)
  refine ⟨hRint, ?_⟩
  have hI := integral_mono_ae hRint (hQint.const_mul ε) hMod
  simpa only [integral_const_mul] using hI
