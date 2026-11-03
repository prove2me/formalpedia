-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_history_weighted_cross_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:53:36.747297+00:00
-- url     : https://prove2.me/submissions/cb564cc2-c35b-4394-8eeb-9fcb645353dc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero

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
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (G : Ω → ℝ)
    (hG : Measurable[𝓕.rightCont u] G)
    (hProdI : Integrable (fun ω =>
      (G ω * (X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c)) *
      (X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c)) P) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    P[(G * Y₁) * Y₂ | 𝓕.rightCont u] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y₁ : Ω → ℝ := fun ω =>
    X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  let Y₂ : Ω → ℝ := fun ω =>
    X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
  have hsMeas : Measurable[𝓕.rightCont u] (X.X s) :=
    (X.adapted s).mono
      ((𝓕.mono (hst.trans htu)).trans (𝓕.le_rightCont u)) le_rfl
  have htMeas : Measurable[𝓕.rightCont u] (X.X t) :=
    (X.adapted t).mono ((𝓕.mono htu).trans (𝓕.le_rightCont u)) le_rfl
  have hY₁Meas : Measurable[𝓕.rightCont u] Y₁ :=
    (htMeas.sub hsMeas).sub_const (((t - s) : ℝ) * X.c)
  have hGY₁Strong : StronglyMeasurable[𝓕.rightCont u] (G * Y₁) :=
    (hG.mul hY₁Meas).stronglyMeasurable
  have hY₂Pair :=
    avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
      X hν u v huv
  change Integrable Y₂ P ∧
    (P[Y₂ | 𝓕.rightCont u] =ᵐ[P] (fun _ => (0 : ℝ))) at hY₂Pair
  have hPull :
      P[(G * Y₁) * Y₂ | 𝓕.rightCont u] =ᵐ[P]
        (G * Y₁) * P[Y₂ | 𝓕.rightCont u] :=
    condExp_mul_of_stronglyMeasurable_left hGY₁Strong hProdI hY₂Pair.1
  change P[(G * Y₁) * Y₂ | 𝓕.rightCont u] =ᵐ[P]
    (fun _ => (0 : ℝ))
  filter_upwards [hPull, hY₂Pair.2] with ω hp hz
  calc
    (P[(G * Y₁) * Y₂ | 𝓕.rightCont u]) ω =
        ((G * Y₁) * P[Y₂ | 𝓕.rightCont u]) ω := hp
    _ = (G ω * Y₁ ω) * (P[Y₂ | 𝓕.rightCont u]) ω := rfl
    _ = 0 := by rw [hz]; ring
