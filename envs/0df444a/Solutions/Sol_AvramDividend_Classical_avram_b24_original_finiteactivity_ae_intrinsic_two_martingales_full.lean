-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_ae_intrinsic_two_martingales_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:24:27.716054+00:00
-- url     : https://prove2.me/submissions/9d90aaaf-79bf-4b8e-a0d8-db6f3ad74643

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) :
    (∀ u : ℝ≥0, Integrable (R u) P) ∧
    (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
    (∀ a b : ℝ≥0, a ≤ b →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
    (∀ a b : ℝ≥0, a ≤ b →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω)  := by
  let τ : Ω → ℝ≥0 := fun _ => 0
  have hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) := by
    first
    | exact isStoppingTime_const 𝓕.rightCont (0 : ℝ≥0)
    | exact isStoppingTime_const (𝓕 := 𝓕.rightCont) (0 : ℝ≥0)
    | change ∀ t : ℝ≥0, MeasurableSet[𝓕.rightCont t]
        {ω : Ω | (0 : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}
      intro t
      simp
  have hCut : ∀ᵐ ω ∂P, ∀ k : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k (0 : ℝ≥0) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k (0 : ℝ≥0) ω =
      (((0 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν)) := by
    filter_upwards [] with ω
    intro k
    simp
  obtain ⟨R0, J0, hR0, hJ0, hRI, hJI, hRM, hJM, _⟩ :=
    avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
      X hX hFinite 1 (by omega) τ hτstop (by intro ω; simp [τ])
      ({0} : Finset ℝ≥0) (by intro ω; simp [τ])
      (fun _ => (0 : ℝ≥0)) (fun _ => (0 : ℝ≥0)) hCut
  have hRequal (u : ℝ≥0) : R u =ᵐ[P] R0 u := by
    filter_upwards [hRsource, hR0] with ω h1 h2
    exact tendsto_nhds_unique (h1 u) (h2 u)
  have hJequal (u : ℝ≥0) : Jsmall u =ᵐ[P] J0 u := by
    filter_upwards [hJsource, hJ0] with ω h1 h2
    exact tendsto_nhds_unique (h1 u) (h2 u)
  refine ⟨(fun u => (hRI u).congr (hRequal u).symm),
    (fun u => (hJI u).congr (hJequal u).symm), ?_, ?_⟩
  · intro a b hab
    calc
      P[R b | 𝓕.rightCont a] =ᵐ[P]
          P[R0 b | 𝓕.rightCont a] :=
        condExp_congr_ae (hRequal b)
      _ =ᵐ[P] R0 a := hRM a b hab
      _ =ᵐ[P] R a := (hRequal a).symm
  · intro a b hab
    calc
      P[Jsmall b | 𝓕.rightCont a] =ᵐ[P]
          P[J0 b | 𝓕.rightCont a] :=
        condExp_congr_ae (hJequal b)
      _ =ᵐ[P] J0 a := hJM a b hab
      _ =ᵐ[P] Jsmall a := (hJequal a).symm
