-- Prove2me | solution 1 for AvramDividend.Classical.avram_b210_original_canonical_ruinclipped_mixed_energy_from_intrinsic_gaussian_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:12:32.088164+00:00
-- url     : https://prove2.me/submissions/035955e2-8240-423a-8b23-b64c1208cfc1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
import Theorems.Thm_AvramDividend_Classical_avram_b208_original_canonical_ruinclipped_mixed_source_energy_without_count_assumptions
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- True source stopped Gaussian-jump mixed energy from the conull original intrinsic-noise decomposition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (hx : 0 < x) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d : ℝ) (R Jsmall : ℝ≥0 → Ω → ℝ)
    (grid : Ω → ℕ → ℝ≥0)
    (hGridMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hGridBound : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ (n : ℝ≥0))
    (hGridEndpoints : ∀ ω i, i ∈ S →
      s i ω = grid ω i ∧ t i ω = grid ω (i + 1))
    (hJcanon : ∀ ω i, i ∈ J ω ↔ i ∈ S ∧
      ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hRsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j u ω)
        atTop (𝓝 (R u ω)))
    (hJsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X j u ω)
        atTop (𝓝 (Jsmall u ω)))
    (hV : ∀ ω i, i ∈ S →
      V i ω = R (t i ω) ω - R (s i ω) ω)
    (hd : d = -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞))
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P) :
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (x + ((k : ℝ) + 1) + ((n : ℝ≥0) : ℝ) * |X.c|)^2 * (((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by
  classical
  intro E G Denergy
  have hJcanonSt (ω : Ω) (i : ℕ) :
      i ∈ J ω ↔ i ∈ S ∧ ∃ u : ℝ≥0,
        s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    constructor
    · intro hi
      obtain ⟨hiS, u, hsu, hut, hne⟩ := (hJcanon ω i).mp hi
      obtain ⟨hsEq, htEq⟩ := hGridEndpoints ω i hiS
      exact ⟨hiS, ⟨u, by simpa only [hsEq] using hsu,
        by simpa only [htEq] using hut, hne⟩⟩
    · rintro ⟨hiS, u, hsu, hut, hne⟩
      obtain ⟨hsEq, htEq⟩ := hGridEndpoints ω i hiS
      apply (hJcanon ω i).mpr
      exact ⟨hiS, ⟨u, by simpa only [hsEq] using hsu,
        by simpa only [htEq] using hut, hne⟩⟩
  have hSplit :=
    avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
      X hFinite R Jsmall hRsrc hJsrc S s t
      (fun ω i hi => (hInterior ω i hi).1) J hJcanonSt
  have hNoJump : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ) := by
    filter_upwards [hSplit] with ω hω
    intro i hi hnot
    have heq := hω i hi hnot
    rw [hV ω i hi, hd]
    exact heq
  exact avram_b208_original_canonical_ruinclipped_mixed_source_energy_without_count_assumptions
    X hFinite x hx C D hD n ρ hρbound hρclip κ hκexact
    k S s t V J d grid hGridMono hGridMeas hGridBound
    hGridEndpoints hJcanon hInterior hNoJump hsStop htStop hGI
