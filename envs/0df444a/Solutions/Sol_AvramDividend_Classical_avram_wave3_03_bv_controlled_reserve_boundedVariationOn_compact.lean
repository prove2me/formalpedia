-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:15:04.408823+00:00
-- url     : https://prove2.me/submissions/a67f4ffe-d869-44ce-98a9-9976fb303587

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_partition_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BoundedVariationOn (fun t : ℝ≥0 => riskProcess X x D t ω) (Icc 0 T) := by
  have hd : 0 ≤ X.drift := le_of_lt (bv_standing_drift_pos X hX hBV).1
  filter_upwards [
    bv_actual_levy_residual_ae_monotone_all_times X hBV,
    avram_wave3_03_bv_controlled_reserve_partition_variation X hX hBV x D hD
  ] with ω hres hpart
  intro T
  let K : ℝ := 2 * X.drift * (T : ℝ) -
    (X.X T ω - X.X 0 ω) + (D T ω - D 0 ω)
  have hDmono : Monotone (fun t : ℝ≥0 => D t ω) := hD.2.1 ω
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
        |riskProcess X x D (u (i + 1)) ω - riskProcess X x D (u i) ω|) ≤ K := by
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
        edist (riskProcess X x D (u (i + 1)) ω) (riskProcess X x D (u i) ω)) =
      ENNReal.ofReal (∑ i ∈ Finset.range n,
        |riskProcess X x D (u (i + 1)) ω - riskProcess X x D (u i) ω|) := by
    calc
      _ = ∑ i ∈ Finset.range n, ENNReal.ofReal
          |riskProcess X x D (u (i + 1)) ω - riskProcess X x D (u i) ω| := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [edist_dist, Real.dist_eq]
      _ = _ := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro i hi
        exact abs_nonneg _
  have hvar :
      eVariationOn (fun t : ℝ≥0 => riskProcess X x D t ω) (Icc 0 T) ≤
        ENNReal.ofReal K := by
    unfold eVariationOn
    refine iSup_le fun p => ?_
    obtain ⟨n, ⟨u, hu, hus⟩⟩ := p
    rw [hsums u n]
    exact ENNReal.ofReal_le_ofReal (hgrid u hu hus n)
  change eVariationOn (fun t : ℝ≥0 => riskProcess X x D t ω) (Icc 0 T) ≠ ⊤
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
