-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_summable_annulus_centered_L2_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:45:41.085191+00:00
-- url     : https://prove2.me/submissions/7d5c85e1-bcca-43c2-89db-5a7f3165be3b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf19_original_finite_spatial_annulus_weighted_centered_L2
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf18_original_summable_annulus_partial_sums_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal Topology
noncomputable section

/-- The actual compensated physical negative-annulus partial sums converge
in centred L2 when their spatial variance energies are summable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ Finset.range k, a i * ((N i ω).toReal - r i)
    Summable (fun i => (a i) ^ 2 * r i) →
      ∃ M : ℕ → Lp ℝ (2 : ℝ≥0∞) P,
        (∀ k, (M k : Ω → ℝ) =ᵐ[P] S k) ∧
        ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
          Tendsto M Filter.atTop (𝓝 L) ∧
          (∫ ω, L ω ∂P) = 0 := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i)
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let S : ℕ → Ω → ℝ := fun k ω =>
    ∑ i ∈ Finset.range k, a i * ((N i ω).toReal - r i)
  change Summable (fun i => (a i) ^ 2 * r i) →
    ∃ M : ℕ → Lp ℝ (2 : ℝ≥0∞) P,
      (∀ k, (M k : Ω → ℝ) =ᵐ[P] S k) ∧
      ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
        Tendsto M Filter.atTop (𝓝 L) ∧
        (∫ ω, L ω ∂P) = 0
  intro hSumm
  have hFinite :=
    avram_mix_inf19_original_finite_spatial_annulus_weighted_centered_L2
      X T cut hcut a
  change ∀ k, MemLp (S k) 2 P ∧ (∫ ω, S k ω ∂P) = 0 at hFinite
  have hTail :=
    avram_mix_inf18_original_summable_annulus_partial_sums_L2_cauchy
      X T cut hcut a hSumm
  change ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n m : ℕ, n₀ ≤ n → n₀ ≤ m →
        Integrable (fun ω => (S n ω - S m ω) ^ 2) P ∧
        (∫ ω, (S n ω - S m ω) ^ 2 ∂P) < ε at hTail
  have hPair (n m : ℕ) : MemLp (S n - S m) 2 P :=
    (hFinite n).1.sub (hFinite m).1
  have hEnergy : Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, (S nm.1 ω - S nm.2 ω) ^ 2 ∂P) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hTail ε hε
    refine ⟨(n₀, n₀), ?_⟩
    intro ⟨n, m⟩ hnm
    have hle : n₀ ≤ n ∧ n₀ ≤ m := hnm
    have hBound := (hn₀ n m hle.1 hle.2).2
    have hNonneg : 0 ≤ ∫ ω, (S n ω - S m ω) ^ 2 ∂P :=
      integral_nonneg (fun ω => sq_nonneg _)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg] using hBound
  have hENorm :=
    avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy P S hPair hEnergy
  let M : ℕ → Lp ℝ (2 : ℝ≥0∞) P :=
    fun k => (hFinite k).1.toLp (S k)
  have hAE (k : ℕ) : (M k : Ω → ℝ) =ᵐ[P] S k :=
    (hFinite k).1.coeFn_toLp
  have hEq (n m : ℕ) :
      eLpNorm ((M n : Ω → ℝ) - (M m : Ω → ℝ)) 2 P =
        eLpNorm (S n - S m) 2 P :=
    eLpNorm_congr_ae ((hAE n).sub (hAE m))
  have hNorm : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm ((M nm.1 : Ω → ℝ) - (M nm.2 : Ω → ℝ)) 2 P)
      atTop (𝓝 0) := by
    have hFun : (fun nm : ℕ × ℕ =>
        eLpNorm ((M nm.1 : Ω → ℝ) - (M nm.2 : Ω → ℝ)) 2 P) =
        (fun nm : ℕ × ℕ => eLpNorm (S nm.1 - S nm.2) 2 P) := by
      funext nm
      exact hEq nm.1 nm.2
    rw [hFun]
    exact hENorm
  have hCauchy : CauchySeq M :=
    (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm M).mpr hNorm
  have hMean (k : ℕ) : (∫ ω, M k ω ∂P) = 0 := by
    calc
      (∫ ω, M k ω ∂P) = (∫ ω, S k ω ∂P) := integral_congr_ae (hAE k)
      _ = 0 := (hFinite k).2
  refine ⟨M, hAE, ?_⟩
  exact avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
    X M hCauchy hMean
