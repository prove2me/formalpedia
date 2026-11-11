-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger68_original_clipped_source_observable_envelope_package
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:42:27.470347+00:00
-- url     : https://prove2.me/submissions/97e44a9a-e5d2-4e1a-b6fc-6b70c043cf03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger69_original_clipped_source_cell_exponential_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger71_original_clipped_source_joint_measurability
import Theorems.Thm_AvramDividend_Classical_avram_gledger72_original_clipped_source_active_cell_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical observables and one-sided active-cell envelopes
    imply the exact source package; integrability follows from gledger69. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      let S : Ω → ℝ := fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))
      ∃ (hFinite : IsFiniteMeasure P), ∃ θ K b : ℝ,
        0 ≤ K ∧ 0 ≤ b ∧
        AEStronglyMeasurable S P ∧
        (∀ ω i, 0 ≤ E i ω) ∧
        (∀ ω i, E i ω ≤ 1) ∧
        (∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
          (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
          (-b ≤ w (Y i ω) ∧
            w (Z i ω) ≤ K * Real.exp (θ * Z i ω))) ∧
        (∀ i ∈ Finset.range (m + 1),
          Integrable (fun ω => Real.exp (θ * Z i ω)) P) := by
  intro m Δ v E Y Z S
  letI : IsProbabilityMeasure P := X.isProbability
  have hFinite : IsFiniteMeasure P := inferInstance
  obtain ⟨hSmeas, hExpMeas, hvreal, hvstop, hd0, hρbound⟩ :=
    avram_gledger71_original_clipped_source_joint_measurability
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  obtain ⟨θ, K, b, hθ, hK, hb, hcell⟩ :=
    avram_gledger72_original_clipped_source_active_cell_envelope
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  refine ⟨hFinite, θ, K, b, hK, hb, hSmeas, ?_, ?_, hcell, ?_⟩
  · intro ω i
    exact Real.exp_nonneg _
  · intro ω i
    change Real.exp (-(q * (v i ω : ℝ))) ≤ 1
    have hv : 0 ≤ (v i ω : ℝ) := by positivity
    have harg : -(q * (v i ω : ℝ)) ≤ 0 := by
      exact neg_nonpos.mpr (mul_nonneg (le_of_lt hq) hv)
    simpa using (Real.exp_le_exp.mpr harg)
  · intro i hi
    have hDs : IsDividendStrategy 𝓕 D := hD.1.1
    have hd0all : ∀ (t : ℝ≥0) (ω : Ω), 0 ≤ rightLimit D t ω := by
      intro t ω
      have hzero : 0 ≤ D t ω := by
        have hm := (hDs.2.1 ω) (show (0 : ℝ≥0) ≤ t from bot_le)
        simpa [hDs.1 ω] using hm
      exact hzero.trans (dividendStrategy_le_rightLimit D hDs ω t)
    have hd0full : ∀ (k : ℝ≥0) (ω : Ω),
        0 ≤ rightLimit D (min (k * Δ) (ρ ω)) ω := by
      intro k ω
      exact hd0all _ _
    exact (avram_gledger69_original_clipped_source_cell_exponential_L1
      X θ hθ x D Δ (n : ℝ≥0) ρ hρbound hvreal hvstop hd0full
      (hExpMeas θ)) i
