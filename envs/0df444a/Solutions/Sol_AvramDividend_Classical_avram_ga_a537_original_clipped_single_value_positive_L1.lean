-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a537_original_clipped_single_value_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:42:44.781143+00:00
-- url     : https://prove2.me/submissions/daa2c420-e416-4562-b2c7-2799aa9a3db5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_gledger68_original_clipped_source_observable_envelope_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a535_active_positive_domain_spatial_cell_aemeasurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
import Theorems.Thm_AvramDividend_Classical_avram_ga_a536_clipped_active_cell_one_sided_exponential_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let A : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun a =>
        x + X.X (v (a + 1)) ω - rightLimit D (v a) ω
      if 0 < ρ ω then E (v (i + 1)) * (w (Z i) - w (Y (v i)))
      else 0
    ∀ m i : ℕ, i < m → Integrable (fun ω => max (A m i ω) (0 : ℝ)) P := by
  classical
  intro A m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 := fun a ω => min ((a : ℝ≥0) * Δ) (ρ ω)
  let E : ℕ → Ω → ℝ := fun a ω => Real.exp (-(q * (v a ω : ℝ)))
  let Y : ℕ → Ω → ℝ := fun a ω =>
    x + X.X (v a ω) ω - rightLimit D (v a ω) ω
  let Z : ℕ → Ω → ℝ := fun a ω =>
    x + X.X (v (a + 1) ω) ω - rightLimit D (v a ω) ω
  obtain ⟨hEM, hYM, hZM, hAlt⟩ :=
    avram_ga_a43_original_clipped_spatial_cell_observations
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
      x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m
  obtain ⟨hFinite, θ, K, b, hK, hb, _, hE0, hE1, hCell, hExp⟩ :=
    avram_gledger68_original_clipped_source_observable_envelope_package
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
      x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m
  letI : IsFiniteMeasure P := hFinite
  have him : i ∈ Finset.range (m + 1) := by
    exact Finset.mem_range.mpr (lt_trans hi (Nat.lt_succ_self m))
  have hPos : ∀ᵐ ω ∂P,
      Y i ω = Z i ω ∨ (0 < Y i ω ∧ 0 < Z i ω) := by
    filter_upwards [hAlt] with ω hw
    rcases hw i him with hh | hh
    · exact Or.inl hh.2.symm
    · exact Or.inr hh
  have hVal : AEStronglyMeasurable
      (fun ω => E (i + 1) ω * (w (Z i ω) - w (Y i ω))) P := by
    apply avram_ga_a535_active_positive_domain_spatial_cell_aemeasurable
    · exact avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
        w C hTopCap hw_smooth
    · exact hYM i
    · exact hZM i
    · exact hEM (i + 1)
    · filter_upwards [hPos] with ω hω
      rcases hω with hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
  have hActive : ∀ᵐ ω ∂P,
      Z i ω = Y i ω ∨
        (-b ≤ w (Y i ω) ∧ 0 < Z i ω ∧
          w (Z i ω) ≤ K * Real.exp (θ * Z i ω)) := by
    filter_upwards [hCell, hAlt] with ω hc ha
    rcases ha i him with hsame | hpositive
    · exact Or.inl hsame.2
    · rcases hc i him with hsame | hgood
      · exact Or.inl hsame.2
      · exact Or.inr ⟨hgood.1,hpositive.2,hgood.2⟩
  have hI := avram_ga_a536_clipped_active_cell_one_sided_exponential_L1
    w (E (i+1)) (Y i) (Z i) θ K b hK hb
    (Filter.Eventually.of_forall fun ω => ⟨hE0 ω (i+1),hE1 ω (i+1)⟩)
    hActive (hExp i him)
    ((continuous_id.max continuous_const).comp_aestronglyMeasurable hVal)
  have hEq (ω : Ω) :
      (if 0 < ρ ω then
        E (i+1) ω * (w (Z i ω) - w (Y i ω))
       else 0) = E (i+1) ω * (w (Z i ω) - w (Y i ω)) := by
    by_cases hρ : 0 < ρ ω
    · simp [hρ]
    · have hz : ρ ω = 0 := le_antisymm (le_of_not_gt hρ) bot_le
      simp [v,Y,Z,hz]
  change Integrable (fun ω => max
    (if 0 < ρ ω then E (i+1) ω * (w (Z i ω) - w (Y i ω)) else 0)
    (0 : ℝ)) P
  exact hI.congr (Filter.Eventually.of_forall fun ω => by
    exact congrArg (fun z : ℝ => max z 0) (hEq ω).symm)
