-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a553_original_clipped_spatial_positive_exponential_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:16:54.430254+00:00
-- url     : https://prove2.me/submissions/7ec99b09-95ad-44b7-8572-82b4973977bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_ga_a554_discounted_difference_positive_exp_upper
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
      if 0 < ρ ω then E (v (i + 1)) * (w (Z i) - w (Y (v i))) else 0
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    ∃ θ K L : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ L ∧
      ∀ m i : ℕ, i < m → ∀ᵐ ω ∂P,
        max (A m i ω) (0 : ℝ) ≤
          K * Real.exp (θ * Z m i ω) + L := by
  classical
  intro A Z
  obtain ⟨θ,K,hθ,hK,hUpper⟩ :=
    avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
      X hNuZero hSigmaNonzero q hq w C hTopCap hw_smooth hw_gen
  obtain ⟨M,hM,hJet⟩ :=
    avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
      X x hx D hD.1.1 w C hTopCap hw_smooth ρ j hprefix
  refine ⟨θ,K,M,hθ,hK,hM,?_⟩
  intro m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 := fun k ω => min ((k : ℝ≥0) * Δ) (ρ ω)
  let E : ℕ → Ω → ℝ := fun k ω => Real.exp (-(q * (v k ω : ℝ)))
  let Y : ℕ → Ω → ℝ := fun k ω =>
    x + X.X (v k ω) ω - rightLimit D (v k ω) ω
  have hObs :=
    avram_ga_a43_original_clipped_spatial_cell_observations
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  filter_upwards [hJet, hObs.2.2.2] with ω hj hAlt
  have hnonneg : 0 ≤ K * Real.exp (θ * Z m i ω) + M :=
    add_nonneg (mul_nonneg hK (Real.exp_pos _).le) hM
  by_cases hr : 0 < ρ ω
  · rcases hAlt i (Finset.mem_range.mpr (by omega : i < m+1)) with hzero | hpos
    · have hEq : Z m i ω = Y i ω := hzero.2
      have hA : A m i ω = 0 := by
        change (if 0 < ρ ω then
          E (i+1) ω * (w (Z m i ω) - w (Y i ω)) else 0) = 0
        simp [hr, hEq]
      simp [hA, hnonneg]
    · by_cases hv : v i ω < ρ ω
      · have hY := (hj (v i ω) hv).1
        have hZ := hUpper (Z m i ω) hpos.2
        have he0 : 0 ≤ E (i+1) ω :=
          (Real.exp_pos _).le
        have he1 : E (i+1) ω ≤ 1 := by
          apply (Real.exp_le_one_iff).2
          exact neg_nonpos.mpr (mul_nonneg hq.le (by positivity))
        have hb := avram_ga_a554_discounted_difference_positive_exp_upper
          (w (Z m i ω)) (w (Y i ω)) (E (i+1) ω)
          θ K M (Z m i ω) hK hM he0 he1 hZ hY
        simpa only [A, E,Y,v,Δ, if_pos hr] using hb
      · have hvi : v i ω = ρ ω :=
          le_antisymm (min_le_right _ _) (le_of_not_gt hv)
        have hvi1 : v (i+1) ω = ρ ω := by
          have hm : ρ ω ≤ (i : ℝ≥0) * Δ := by
            exact (min_eq_right_iff.mp hvi)
          have hn : (i : ℝ≥0) * Δ ≤ ((i+1 : ℕ) : ℝ≥0) * Δ := by
            gcongr
            omega
          exact min_eq_right (hm.trans hn)
        have hEq : Z m i ω = Y i ω := by
          change x + X.X (v (i+1) ω) ω - rightLimit D (v i ω) ω =
            x + X.X (v i ω) ω - rightLimit D (v i ω) ω
          rw [hvi1, hvi]
        have hA : A m i ω = 0 := by
          change (if 0 < ρ ω then
            E (i+1) ω * (w (Z m i ω) - w (Y i ω)) else 0) = 0
          simp [hr, hEq]
        simp [hA, hnonneg]
  · have hA : A m i ω = 0 := by simp [A,hr]
    simp [hA, hnonneg]
