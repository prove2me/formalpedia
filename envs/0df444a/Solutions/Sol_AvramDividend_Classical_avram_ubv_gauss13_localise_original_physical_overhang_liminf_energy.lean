-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_overhang_liminf_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:57:29.144795+00:00
-- url     : https://prove2.me/submissions/0f4ee25b-ebff-4d6a-97cb-1a1edb8db43a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ ρ : Ω → ℝ≥0)
    (s : ℕ → Ω → ℝ≥0)
    (hSourceLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (s n ω) ω -
        (s n ω : ℝ) * X.c) atTop
        (𝓝 (X.X (τ ω) ω - (τ ω : ℝ) * X.c)))
    (hMeas : ∀ n, Measurable (fun ω : Ω =>
      ENNReal.ofReal
        (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
          (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2))) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) ^ 2) ∂P) ≤
      Filter.liminf (fun n =>
        ∫⁻ ω, ENNReal.ofReal
          (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
            (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2) ∂P)
      atTop := by
  let B : Ω → ℝ := fun ω => X.X (ρ ω) ω - (ρ ω : ℝ) * X.c
  let A : ℕ → Ω → ℝ := fun n ω => X.X (s n ω) ω -
    (s n ω : ℝ) * X.c
  let L : Ω → ℝ := fun ω => X.X (τ ω) ω - (τ ω : ℝ) * X.c
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal ((B ω - A n ω) ^ 2)
  change (∫⁻ ω, ENNReal.ofReal ((B ω - L ω) ^ 2) ∂P) ≤
    Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop
  have hFMeas (n : ℕ) : Measurable (F n) := hMeas n
  have hFlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop
        (𝓝 (ENNReal.ofReal ((B ω - L ω) ^ 2))) := by
    filter_upwards [hSourceLimit] with ω hω
    have hsub : Tendsto (fun n => B ω - A n ω) atTop
        (𝓝 (B ω - L ω)) :=
      tendsto_const_nhds.sub hω
    have hsq := hsub.pow 2
    exact (ENNReal.continuous_ofReal.tendsto ((B ω - L ω) ^ 2)).comp hsq
  have hLeft : (fun ω => ENNReal.ofReal ((B ω - L ω) ^ 2)) =ᵐ[P]
      (fun ω => Filter.liminf (fun n => F n ω) atTop) := by
    filter_upwards [hFlim] with ω hω
    exact hω.liminf_eq.symm
  calc
    (∫⁻ ω, ENNReal.ofReal ((B ω - L ω) ^ 2) ∂P) =
        (∫⁻ ω, Filter.liminf (fun n => F n ω) atTop ∂P) :=
      lintegral_congr_ae hLeft
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop :=
      lintegral_liminf_le (μ := P) (u := atTop) (f := F) hFMeas
