-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb19_original_gaussian_source_totalised_martingale_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:18:18.21561+00:00
-- url     : https://prove2.me/submissions/1a2c5692-b738-4a9d-9a70-d0b9f6cbcb7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18t_original_J_physical_jump_decomposition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Transfer physical Gaussian residual martingale and second-moment data to a
pathwise-total exact Lévy source decomposition in the original filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      (∀ t : ℝ≥0, Integrable (M t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (M t) ω = M s ω) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ω => (M t ω) ^ 2) P ∧
        (∫ ω, (M t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω
  have hsource :=
    avram_ja18t_original_J_physical_jump_decomposition
      X R Jsmall hRsource hJsource
  have hMeq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω := by
    filter_upwards [hsource] with ω hω
    intro t
    dsimp [M]
    have ht := hω t
    linear_combination ht
  refine ⟨M, ?_, hMeq, ?_, ?_, ?_⟩
  · intro t ω
    dsimp [M]
    ring
  · intro t
    have ht : M t =ᵐ[P] R t := hMeq.mono (fun ω hω => hω t)
    exact (hRint t).congr ht.symm
  · intro s t hst
    have ht : M t =ᵐ[P] R t := hMeq.mono (fun ω hω => hω t)
    have hs : M s =ᵐ[P] R s := hMeq.mono (fun ω hω => hω s)
    have hCE :
        condExp (𝓕.rightCont s) P (M t) =ᵐ[P]
          condExp (𝓕.rightCont s) P (R t) :=
      condExp_congr_ae ht
    filter_upwards [hCE, hRmart s t hst, hs] with ω hce hm hr
    calc
      condExp (𝓕.rightCont s) P (M t) ω =
          condExp (𝓕.rightCont s) P (R t) ω := hce
      _ = R s ω := hm
      _ = M s ω := hr.symm
  · intro t
    obtain ⟨hR2, hRmoment⟩ := hRbracket t
    have ht : M t =ᵐ[P] R t := hMeq.mono (fun ω hω => hω t)
    have hsq :
        (fun ω => (M t ω) ^ 2) =ᵐ[P]
          (fun ω => (R t ω) ^ 2) := by
      filter_upwards [ht] with ω hω
      rw [hω]
    refine ⟨hR2.congr hsq.symm, ?_⟩
    calc
      (∫ ω, (M t ω) ^ 2 ∂P) =
          (∫ ω, (R t ω) ^ 2 ∂P) := integral_congr_ae hsq
      _ = (t : ℝ) * X.σ ^ 2 := hRmoment
