-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_predictable_L2_bilinear_cross_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:31:56.082326+00:00
-- url     : https://prove2.me/submissions/3e531b81-ed16-4f6c-b013-975b38e01e9f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_history_weighted_cross_condExp_zero

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
    (G H : Ω → ℝ)
    (hG : Measurable[𝓕.rightCont u] G)
    (hH : Measurable[𝓕.rightCont u] H)
    (hM1 : MemLp (fun ω =>
      G ω * (X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c)) 2 P)
    (hM2 : MemLp (fun ω =>
      H ω * (X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c)) 2 P) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    Integrable ((G * Y₁) * (H * Y₂)) P ∧
      (P[(G * Y₁) * (H * Y₂) | 𝓕.rightCont u] =ᵐ[P]
        (fun _ => (0 : ℝ))) := by
  let Y₁ : Ω → ℝ := fun ω =>
    X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  let Y₂ : Ω → ℝ := fun ω =>
    X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
  have hCrossI : Integrable ((G * Y₁) * (H * Y₂)) P :=
    hM1.integrable_mul hM2
  have hCell :
      (G * Y₁) * (H * Y₂) =
      ((fun ω => G ω * H ω) * Y₁) * Y₂ := by
    funext ω
    change (G ω * Y₁ ω) * (H ω * Y₂ ω) =
      ((G ω * H ω) * Y₁ ω) * Y₂ ω
    ring
  have hProductI : Integrable
      (((fun ω => G ω * H ω) * Y₁) * Y₂) P := by
    rw [← hCell]
    exact hCrossI
  have hBase :
      P[((fun ω => G ω * H ω) * Y₁) * Y₂ | 𝓕.rightCont u] =ᵐ[P]
        (fun _ => (0 : ℝ)) :=
    avram_wave6_03_original_rightCont_gaussian_disjoint_history_weighted_cross_condExp_zero
      X hν s t u v hst htu huv (fun ω => G ω * H ω)
        (hG.mul hH) hProductI
  change Integrable ((G * Y₁) * (H * Y₂)) P ∧
    (P[(G * Y₁) * (H * Y₂) | 𝓕.rightCont u] =ᵐ[P]
      (fun _ => (0 : ℝ)))
  refine ⟨hCrossI, ?_⟩
  rw [hCell]
  exact hBase
