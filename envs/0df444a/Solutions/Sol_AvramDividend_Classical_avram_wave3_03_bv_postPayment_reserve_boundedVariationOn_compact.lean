-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_reserve_boundedVariationOn_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:34:35.310567+00:00
-- url     : https://prove2.me/submissions/2c0a542c-a5b5-4dc1-a09f-533e68234a5f

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_reserve_partition_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The real post-payment controlled reserve has finite variation on every
    deterministic compact interval, including the initial dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BoundedVariationOn
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (Icc 0 T) := by
  have hd : 0 ≤ X.drift := le_of_lt (bv_standing_drift_pos X hX hBV).1
  filter_upwards [
    bv_actual_levy_residual_ae_monotone_all_times X hBV,
    avram_wave3_03_bv_postPayment_reserve_partition_variation X hX hBV x D hD
  ] with ω hres hpart
  intro T
  let K : ℝ := 2 * X.drift * (T : ℝ) -
    (X.X T ω - X.X 0 ω) +
    (rightLimit D T ω - rightLimit D 0 ω)
  have hDmono : Monotone (fun t : ℝ≥0 => rightLimit D t ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have hK : 0 ≤ K := by
    have hr := hres (show (0 : ℝ≥0) ≤ T from zero_le)
    have hc := hDmono (show (0 : ℝ≥0) ≤ T from zero_le)
    have ht : 0 ≤ X.drift * (T : ℝ) :=
      mul_nonneg hd (NNReal.coe_nonneg _)
    dsimp [K] at *
    nlinarith only [hr, hc, ht]
  have hgrid (u : ℕ → ℝ≥0) (hu : Monotone u)
      (hus : ∀ i, u i ∈ Icc (0 : ℝ≥0) T) (n : ℕ) :
      (∑ i ∈ Finset.range n,
        |(x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          (x + X.X (u i) ω - rightLimit D (u i) ω)|) ≤ K := by
    have htime : (u n : ℝ) - (u 0 : ℝ) ≤ (T : ℝ) := by
      have h0 : 0 ≤ (u 0 : ℝ) := NNReal.coe_nonneg _
      have hn : (u n : ℝ) ≤ (T : ℝ) := by
        exact_mod_cast (hus n).2
      linarith
    have hdt := mul_le_mul_of_nonneg_left htime hd
    have hrlo := hres (show (0 : ℝ≥0) ≤ u 0 from zero_le)
    have hrhi := hres (hus n).2
    have hDlo := hDmono (show (0 : ℝ≥0) ≤ u 0 from zero_le)
    have hDhi := hDmono (hus n).2
    have hv := hpart u hu n
    dsimp [K] at *
    nlinarith only [hdt, hrlo, hrhi, hDlo, hDhi, hv]
  have hsums (u : ℕ → ℝ≥0) (n : ℕ) :
      (∑ i ∈ Finset.range n,
        edist (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
          (x + X.X (u i) ω - rightLimit D (u i) ω)) =
      ENNReal.ofReal (∑ i ∈ Finset.range n,
        |(x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          (x + X.X (u i) ω - rightLimit D (u i) ω)|) := by
    calc
      _ = ∑ i ∈ Finset.range n, ENNReal.ofReal
          |(x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
            (x + X.X (u i) ω - rightLimit D (u i) ω)| := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [edist_dist, Real.dist_eq]
      _ = _ := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro i hi
        exact abs_nonneg _
  have hvar :
      eVariationOn (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (Icc 0 T) ≤ ENNReal.ofReal K := by
    unfold eVariationOn
    refine iSup_le fun p => ?_
    obtain ⟨n, ⟨u, hu, hus⟩⟩ := p
    rw [hsums u n]
    exact ENNReal.ofReal_le_ofReal (hgrid u hu hus n)
  change eVariationOn
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (Icc 0 T) ≠ ⊤
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
