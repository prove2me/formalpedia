-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a300_true_stopped_fullcell_global_jet_and_HJB_exponential_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:41:42.361776+00:00
-- url     : https://prove2.me/submissions/5e152435-b8e1-46ee-a99f-f8be08eec344

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a163_original_full_mesh_source_endpoint_positive
import Theorems.Thm_AvramDividend_Classical_avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
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
    ∃ θ K M : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        (s < ρ ω ∧ s + Δ ≤ ρ ω) →
          |w y| ≤ M ∧ |deriv w y| ≤ M ∧
          |iteratedDeriv 2 w y| ≤ M ∧
          w (y+r) ≤ K*Real.exp (θ*(y+r)):= by
  obtain ⟨θ,K,hθ,hK,hExp⟩ :=
    avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
      X hNuZero hSigmaNonzero q hq w C hTopCap hw_smooth hw_gen
  obtain ⟨M,hM,hJets⟩ :=
    avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
      X x hx D hD.1.1 w C hTopCap hw_smooth ρ j hprefix
  refine ⟨θ,K,M,hθ,hK,hM,?_⟩
  intro m
  have hPos := avram_ga_a163_original_full_mesh_source_endpoint_positive
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  filter_upwards [hJets,hPos] with ω hJet hPositive
  intro i hi Δ s y r hMask
  have hJ := hJet s hMask.1
  have hY := (hPositive i hi) hMask
  have hSecond : |iteratedDeriv 2 w y| ≤ M := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hJ.2.2
  exact ⟨hJ.1,hJ.2.1,hSecond,hExp (y+r) hY.2⟩
