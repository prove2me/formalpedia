-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_originalLevy_disjointCells_adaptedProducts_L2_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:21:33.456473+00:00
-- url     : https://prove2.me/submissions/ef608768-c8c9-409d-a0b9-762cac1bac8d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Orthogonality of two non-overlapping genuine original Lévy increment
cells with bounded adapted coefficients and bounded earlier payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (H K : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hK : StronglyMeasurable[𝓕 u] K)
    (A B R : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hR0 : 0 ≤ R)
    (hHb : ∀ ω, ‖H ω‖ ≤ A) (hKb : ∀ ω, ‖K ω‖ ≤ B)
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφb : ∀ z, ‖φ z‖ ≤ R)
    (hψInt : Integrable (fun ω => ψ (X.X (v - u) ω)) P)
    (hψMean : (∫ ω, ψ (X.X (v - u) ω) ∂P) = 0) :
    (∫ ω, (H ω * φ (X.X t ω - X.X s ω)) *
      (K ω * ψ (X.X v ω - X.X u ω)) ∂P) = 0 := by
  have hsu : s ≤ u := hst.trans htu
  have hXt : Measurable[𝓕 u] (X.X t) :=
    (X.adapted t).mono (𝓕.mono htu) le_rfl
  have hXs : Measurable[𝓕 u] (X.X s) :=
    (X.adapted s).mono (𝓕.mono hsu) le_rfl
  have hF : StronglyMeasurable[𝓕 u]
      (fun ω => φ (X.X t ω - X.X s ω)) :=
    (hφ.comp (hXt.sub hXs)).stronglyMeasurable
  have hCoeff : StronglyMeasurable[𝓕 u]
      (fun ω => (H ω * φ (X.X t ω - X.X s ω)) * K ω) :=
    ((hH.mono (𝓕.mono hsu)).mul hF).mul hK
  have hCoeffBound : ∀ ω,
      ‖(H ω * φ (X.X t ω - X.X s ω)) * K ω‖ ≤ A * R * B := by
    intro ω
    rw [norm_mul, norm_mul]
    gcongr
    · exact hHb ω
    · exact hφb _
    · exact hKb ω
  have hMean := avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero
    X u v huv ψ hψ
    (fun ω => (H ω * φ (X.X t ω - X.X s ω)) * K ω)
    hCoeff (A * R * B) hCoeffBound hψInt hψMean
  convert hMean using 1
  congr 1
  funext ω
  ring
