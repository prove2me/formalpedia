-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger134_original_positive_clock_uniform_mesh_cash_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:31:44.221165+00:00
-- url     : https://prove2.me/submissions/b1874677-c200-4d3a-9dac-910c7a024f93

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
import Theorems.Thm_AvramDividend_Classical_avram_gledger101_original_strict_clipped_clock_payment_support
import Theorems.Thm_AvramDividend_Classical_avram_gledger113_clipped_crossing_strip_inside_final_mesh
import Theorems.Thm_AvramDividend_Classical_avram_gledger130_finite_partition_cash_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (n m : ℕ)
    (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (k : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    v k < ρ → v (k + 1) = ρ →
    (∀ i : ℕ, i < k → v (i + 1) < ρ) →
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      ((dividendMeasure D ω) ({0} : Set ℝ)).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ : ℝ) - (Δ : ℝ)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  dsimp only
  intro hvk hstop hinterior
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-(q * s)))
  let S : Set ℝ := paymentTimes (ruinTime X x D ω)
  let U : Set ℝ := S ∩ Ioo ((ρ : ℝ) - (Δ : ℝ)) (ρ : ℝ)
  have hgrid := avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
    n m ρ hρn
  have hv : Monotone v := hgrid.1
  have hv0 : v 0 = 0 := hgrid.2.1
  have hvReal : Monotone (fun i : ℕ => (v i : ℝ)) := by
    intro i j hij
    exact_mod_cast (hv hij)
  have hρle : (ρ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hρn
  have hFbound := avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
    D hD.1.1 ω (ruinTime X x D ω) (n : ℝ≥0) q hq
  have hFfin : (∫⁻ s in S ∩ Iio (ρ : ℝ), f s ∂μ) < ⊤ := by
    apply lt_of_le_of_lt _ hFbound
    apply lintegral_mono_set
    intro s hs
    exact ⟨hs.1, le_trans (le_of_lt hs.2) hρle⟩
  have hUfin : (∫⁻ s in U, f s ∂μ) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt _ hFbound
    apply lintegral_mono_set
    intro s hs
    exact ⟨hs.1, le_trans (le_of_lt hs.2.2) hρle⟩
  have hcell : ∀ i < k, Ioc (v i : ℝ) (v (i + 1) : ℝ) ⊆ S := by
    intro i hi s hs
    have hspos : 0 < s := lt_of_le_of_lt (v i).property hs.1
    have hiReal : (v (i + 1) : ℝ) < (ρ : ℝ) :=
      (NNReal.coe_lt_coe).2 (hinterior i hi)
    have hslt : s < (ρ : ℝ) := lt_of_le_of_lt hs.2 hiReal
    exact (avram_gledger101_original_strict_clipped_clock_payment_support
      (ruinTime X x D ω) ρ hρruin ⟨hspos, hslt⟩).1
  have htail : S ∩ Ioo (v k : ℝ) (ρ : ℝ) ⊆ U := by
    intro s hs
    exact ⟨hs.1,
      (avram_gledger113_clipped_crossing_strip_inside_final_mesh
        n m k ρ hvk hstop) hs.2⟩
  have hpart := avram_gledger130_finite_partition_cash_upper_bound
    μ f S (paymentTimes_measurable _) (fun s hs => hs.1)
    (fun i : ℕ => (v i : ℝ)) hvReal
    (congrArg (fun t : ℝ≥0 => (t : ℝ)) hv0)
    k (ρ : ℝ) ((NNReal.coe_lt_coe).2 hvk)
    (congrArg (fun t : ℝ≥0 => (t : ℝ)) hstop)
    hcell hFfin U htail hUfin
  have hμ0 : μ ({0} : Set ℝ) ≠ ⊤ := by
    change (dividendMeasure D ω) ({((0 : ℝ≥0) : ℝ)} : Set ℝ) ≠ ⊤
    rw [dividendMeasure_singleton_eq_rightLimit_sub D hD.1.1 ω 0]
    simp
  have hzeroBound : (∫⁻ s in S ∩ ({0} : Set ℝ), f s ∂μ).toReal ≤
      (μ ({0} : Set ℝ)).toReal := by
    have hh := lintegral_mono_set (μ := μ) (f := f)
      (Set.inter_subset_right : S ∩ ({0} : Set ℝ) ⊆ {0})
    have hsingle : (∫⁻ s in ({0} : Set ℝ), f s ∂μ) = μ {0} := by
      rw [lintegral_singleton]
      simp [f]
    rw [hsingle] at hh
    exact ENNReal.toReal_mono hμ0 hh
  have hupper : (∫⁻ s in S ∩ ({0} : Set ℝ), f s ∂μ).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ), f s ∂μ).toReal) +
      (∫⁻ s in U, f s ∂μ).toReal ≤
      (μ ({0} : Set ℝ)).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ), f s ∂μ).toReal) +
      (∫⁻ s in U, f s ∂μ).toReal := by linarith [hzeroBound]
  simpa only [μ, f, S, U] using hpart.trans hupper
