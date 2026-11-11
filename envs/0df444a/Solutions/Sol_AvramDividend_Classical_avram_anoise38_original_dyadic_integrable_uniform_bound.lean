-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise38_original_dyadic_integrable_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:11:00.730589+00:00
-- url     : https://prove2.me/submissions/c3e21342-7c05-4987-8761-c270009c48b1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_count_ae
import Theorems.Thm_AvramDividend_Classical_avram_anoise39_original_dyadic_mark_partition_count_rate_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise40_finite_weighted_count_rate_abs_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
/-- Original dyadic compensated source admits one integrable pathwise dominator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      ∃ bound : Ω → ℝ, Integrable bound P ∧
        (∀ k, ∀ᵐ ω ∂P, ‖M k ω‖ ≤ bound ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro n s t hst
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → ℕ → Set ℝ := fun k i =>
    B ∩ Ioc (-1 + (i : ℝ) / 2 ^ k) (-1 + ((i : ℝ) + 1) / 2 ^ k)
  let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim
      (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ C k i)
  let M : ℕ → Ω → ℝ := fun k ω =>
    ∑ i ∈ Finset.range (2 ^ k), (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
      ((J k i ω).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim
      (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ Iio (0 : ℝ))
  let R : ℝ := ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  let bound : Ω → ℝ := fun ω => (N ω).toReal ^ 2 + R + 1
  have hNInt : Integrable (fun ω => (N ω).toReal ^ 2) P := by
    simpa only [N] using (avram_anoise18_original_total_negative_count_finite_activity_L2 X hFinite t).1
  have hBoundInt : Integrable bound P :=
    (hNInt.add (integrable_const R)).add (integrable_const 1)
  refine ⟨bound, hBoundInt, ?_⟩
  intro k
  have hfin : ∀ᵐ ω ∂P, N ω < ⊤ := by
    have ht0 : (0 : ℝ≥0) ≤ t := by positivity
    simpa only [N] using
      avram_ubv_mixed12_original_finite_activity_negative_count_ae X 0 t ht0 hFinite
  filter_upwards [hfin] with ω hNfin
  obtain ⟨hCount, hNu⟩ := avram_anoise39_original_dyadic_mark_partition_count_rate_bound X n k s t hst
  have hBsub : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact lt_of_le_of_lt hz.2 (neg_lt_zero.mpr hp)
  have hJcell (i : ℕ) : J k i ω ≤ N ω := by
    dsimp [J, N]
    apply measure_mono
    intro p hp
    have hs0 : (0 : ℝ≥0) ≤ s := by positivity
    exact ⟨⟨lt_of_le_of_lt hs0 hp.1.1, hp.1.2⟩, hBsub hp.2.1⟩
  have hNuCell (i : ℕ) : X.ν (C k i) ≠ ⊤ := by
    have hh : X.ν (C k i) < ⊤ :=
      lt_of_le_of_lt (measure_mono (fun z hz => hBsub hz.1))
        (lt_top_iff_ne_top.mpr hFinite)
    exact ne_top_of_lt hh
  have hJReal :
      (∑ i ∈ Finset.range (2 ^ k), (J k i ω).toReal) ≤ (N ω).toReal := by
    have hc : ∀ i ∈ Finset.range (2 ^ k), J k i ω ≠ ⊤ := by
      intro i hi; exact ne_top_of_lt (lt_of_le_of_lt (hJcell i) hNfin)
    rw [← ENNReal.toReal_sum hc]
    apply (ENNReal.toReal_le_toReal
      (ne_top_of_lt (lt_of_le_of_lt (hCount ω) hNfin))
      (ne_top_of_lt hNfin)).mpr
    exact hCount ω
  have hNuReal :
      (∑ i ∈ Finset.range (2 ^ k), (X.ν (C k i)).toReal) ≤
        (X.ν (Iio (0 : ℝ))).toReal := by
    have hc : ∀ i ∈ Finset.range (2 ^ k), X.ν (C k i) ≠ ⊤ := by
      intro i hi; exact hNuCell i
    rw [← ENNReal.toReal_sum hc]
    apply (ENNReal.toReal_le_toReal
      (ne_top_of_lt (lt_of_le_of_lt hNu (lt_top_iff_ne_top.mpr hFinite)))
      hFinite).mpr
    exact hNu
  have hRateReal :
      (∑ i ∈ Finset.range (2 ^ k),
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal) ≤ R := by
    calc
      (∑ i ∈ Finset.range (2 ^ k),
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
          = (t - s : ℝ≥0).toReal *
              (∑ i ∈ Finset.range (2 ^ k), (X.ν (C k i)).toReal) := by
                simp only [ENNReal.toReal_mul, Finset.mul_sum]; rfl
      _ ≤ (t - s : ℝ≥0).toReal * (X.ν (Iio (0 : ℝ))).toReal :=
        mul_le_mul_of_nonneg_left hNuReal (by positivity)
      _ ≤ (t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast (tsub_le_self : t - s ≤ t)) ENNReal.toReal_nonneg
      _ = R := by simp [R, ENNReal.toReal_mul]
  have hWeight (i : ℕ) (hi : i ∈ Finset.range (2 ^ k)) :
      |-1 + (i : ℝ) / (2 : ℝ) ^ k| ≤ 1 := by
    have hlt : i < 2 ^ k := Finset.mem_range.mp hi
    have hfrac : (i : ℝ) / (2 : ℝ) ^ k ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)).mpr
      exact_mod_cast (Nat.le_of_lt hlt)
    have hnonneg : 0 ≤ (i : ℝ) / (2 : ℝ) ^ k := by positivity
    rw [abs_of_nonpos (by linarith : -1 + (i : ℝ) / (2 : ℝ) ^ k ≤ 0)]
    linarith
  have hWeighted := avram_anoise40_finite_weighted_count_rate_abs_bound
    (Finset.range (2 ^ k)) (fun i => -1 + (i : ℝ) / (2 : ℝ) ^ k)
    (fun i => (J k i ω).toReal)
    (fun i => (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
    hWeight (by intro i hi; exact ENNReal.toReal_nonneg)
    (by intro i hi; exact ENNReal.toReal_nonneg)
  have hNnonneg : 0 ≤ (N ω).toReal := ENNReal.toReal_nonneg
  have hQuad : (N ω).toReal ≤ (N ω).toReal ^ 2 + 1 := by
    nlinarith [sq_nonneg ((N ω).toReal - (1 / 2 : ℝ))]
  have hBase : |M k ω| ≤ (N ω).toReal + R := by
    have hRaw : |M k ω| ≤
        (∑ i ∈ Finset.range (2 ^ k), (J k i ω).toReal) +
        (∑ i ∈ Finset.range (2 ^ k),
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal) := by
      simpa only [M] using hWeighted
    linarith
  change ‖M k ω‖ ≤ bound ω
  dsimp [bound]
  linarith
