-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18n_original_X_centered_rightcont_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:49:14.361897+00:00
-- url     : https://prove2.me/submissions/492e7f43-2612-4f9a-936d-59e06c53dc55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18_standing_X_integrable_fixedtime
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_X_time_mean_triplet
import Theorems.Thm_AvramDividend_Classical_avram_ja18o_original_X_increment_rightcont_condexp_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original right-continuous martingale from the exact original X increment
conditional mean and the time-linear original Lévy first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P
          (fun ω => X.X t ω -
            (t : ℝ) * (∫ η, X.X 1 η ∂P)) ω =
          X.X s ω - (s : ℝ) * (∫ η, X.X 1 η ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let μ : ℝ := ∫ η, X.X 1 η ∂P
  let drift : ℝ := X.c + (∫ z in Iic (-1 : ℝ), z ∂X.ν)
  have hMean (u : ℝ≥0) :
      (∫ η, X.X u η ∂P) = (u : ℝ) * drift :=
    avram_ja18g_original_levy_X_time_mean_triplet X hX hFinite u
  have hμ : μ = drift := by simpa [μ] using hMean 1
  intro s t hst
  let M : ℝ≥0 → Ω → ℝ :=
    fun u ω => X.X u ω - (u : ℝ) * μ
  let D : Ω → ℝ :=
    fun ω => X.X t ω - X.X s ω
  let D0 : Ω → ℝ :=
    fun ω => D ω - ((t : ℝ) - (s : ℝ)) * μ
  have hXt := avram_ja18_standing_X_integrable_fixedtime X hX t
  have hXs := avram_ja18_standing_X_integrable_fixedtime X hX s
  have hDint : Integrable D P := hXt.sub hXs
  have hD0int : Integrable D0 P :=
    hDint.sub (integrable_const _)
  have hMsInt : Integrable (M s) P :=
    hXs.sub (integrable_const _)
  have hMtInt : Integrable (M t) P :=
    hXt.sub (integrable_const _)
  have hMeanD :
      (∫ η, D η ∂P) = ((t : ℝ) - (s : ℝ)) * μ := by
    calc
      (∫ η, D η ∂P) =
          (∫ η, X.X t η ∂P) - (∫ η, X.X s η ∂P) :=
        integral_sub hXt hXs
      _ = (t : ℝ) * drift - (s : ℝ) * drift := by
        rw [hMean t, hMean s]
      _ = ((t : ℝ) - (s : ℝ)) * μ := by rw [hμ]; ring
  have hDCE :=
    avram_ja18o_original_X_increment_rightcont_condexp_mean
      X s t hst hXs hXt
  have hD0CE :
      P[D0 | 𝓕.rightCont s] =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    have hConstInt : Integrable
        (fun _ : Ω => ((t : ℝ) - (s : ℝ)) * μ) P :=
      integrable_const _
    have hSub := condExp_sub hDint hConstInt (𝓕.rightCont s)
    have hConst :
        P[(fun _ : Ω => ((t : ℝ) - (s : ℝ)) * μ) |
          𝓕.rightCont s] =
          (fun _ : Ω => ((t : ℝ) - (s : ℝ)) * μ) :=
      condExp_const (𝓕.rightCont.le s)
        (((t : ℝ) - (s : ℝ)) * μ)
    filter_upwards [hSub, hDCE] with ω hsub hd
    calc
      P[D0 | 𝓕.rightCont s] ω =
          P[D | 𝓕.rightCont s] ω -
          P[(fun _ : Ω => ((t : ℝ) - (s : ℝ)) * μ) |
            𝓕.rightCont s] ω := hsub
      _ = 0 := by
        have hDω : P[D | 𝓕.rightCont s] ω =
            (∫ η, D η ∂P) := by simpa only [D] using hd
        rw [hConst, hDω, hMeanD]
        ring
  have hMsMeas : StronglyMeasurable[𝓕.rightCont s] (M s) := by
    exact (((X.adapted s).mono (𝓕.le_rightCont s) le_rfl).sub
      measurable_const).stronglyMeasurable
  have hSelf : P[M s | 𝓕.rightCont s] = M s :=
    condExp_of_stronglyMeasurable (𝓕.rightCont.le s) hMsMeas hMsInt
  have hEq : M t = M s + D0 := by
    funext ω
    dsimp [M, D, D0]
    ring
  change P[M t | 𝓕.rightCont s] =ᵐ[P] M s
  calc
    P[M t | 𝓕.rightCont s] =ᵐ[P]
        P[M s + D0 | 𝓕.rightCont s] := by rw [hEq]
    _ =ᵐ[P] P[M s | 𝓕.rightCont s] +
        P[D0 | 𝓕.rightCont s] :=
      condExp_add hMsInt hD0int (𝓕.rightCont s)
    _ =ᵐ[P] M s := by
      filter_upwards [hD0CE] with ω hω
      simp [hSelf, hω]
