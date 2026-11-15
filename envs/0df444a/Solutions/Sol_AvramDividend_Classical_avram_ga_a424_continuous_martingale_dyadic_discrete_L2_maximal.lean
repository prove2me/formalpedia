-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a424_continuous_martingale_dyadic_discrete_L2_maximal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:16:26.270082+00:00
-- url     : https://prove2.me/submissions/07f7f788-8ff8-4fff-a9e7-a32a42dc9172

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a426_dyadic_sampled_martingale_L2_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a428_L2_maximal_envelope_integrability_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale M 𝓕 P)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω))
    (T : ℝ≥0)
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    ∀ k : ℕ,
      Integrable (fun ω =>
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)) P ∧
      (∫ ω,
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2) ∂P) ≤
        4 * (∫ ω, (M T ω)^2 ∂P) := by
  classical
  intro k
  let N : ℕ := 2 ^ k
  let f : Ω → ℝ := fun ω => (Finset.range (N + 1)).sup'
    (by simp) (fun i => (M ((i : ℝ≥0) * T / (N : ℝ≥0)) ω)^2)
  let g : Ω → ℝ := fun ω => (Finset.range (N + 1)).sup'
    (by simp) (fun i => |M ((i : ℝ≥0) * T / (N : ℝ≥0)) ω|)
  have hmeas (t : ℝ≥0) : Measurable (M t) :=
    ((hMart.stronglyAdapted t).mono (𝓕.le t)).measurable
  have hf : StronglyMeasurable f := by
    apply Measurable.stronglyMeasurable
    dsimp [f]
    apply Finset.measurable_range_sup''
    intro i hi
    exact (hmeas _).pow_const 2
  have hg : StronglyMeasurable g := by
    apply Measurable.stronglyMeasurable
    dsimp [g]
    apply Finset.measurable_range_sup''
    intro i hi
    exact (hmeas _).abs
  have hfnn (ω : Ω) : 0 ≤ f ω := by
    dsimp [f]
    have h0 := Finset.le_sup'
      (f := fun (i : ℕ) => (M ((i : ℝ≥0) * T / (N : ℝ≥0)) ω)^2)
      (Finset.mem_range.mpr (by positivity : 0 < N + 1))
    nlinarith [sq_nonneg (M ((0 : ℝ≥0) * T / (N : ℝ≥0)) ω)]
  have hdom (ω : Ω) : f ω ≤ (g ω)^2 := by
    dsimp [f,g]
    apply Finset.sup'_le
    intro i hi
    have hle := Finset.le_sup'
      (f := fun (i : ℕ) => |M ((i : ℝ≥0) * T / (N : ℝ≥0)) ω|) hi
    have ha : 0 ≤ |M ((i : ℝ≥0) * T / (N : ℝ≥0)) ω| :=
      abs_nonneg _
    have hb : 0 ≤ (Finset.range (N + 1)).sup' (by simp)
        (fun (j : ℕ) => |M ((j : ℝ≥0) * T / (N : ℝ≥0)) ω|) :=
      le_trans ha hle
    nlinarith [sq_abs (M ((i : ℝ≥0) * T / (N : ℝ≥0)) ω),
      mul_nonneg (sub_nonneg.mpr hle) (add_nonneg ha hb)]
  have hnorm : eLpNorm g 2 P ≤ 2 * eLpNorm (M T) 2 P := by
    simpa [g,N] using
      avram_ga_a426_dyadic_sampled_martingale_L2_norm_bound
        P 𝓕 M hMart T k
  have hres := avram_ga_a428_L2_maximal_envelope_integrability_bridge
    P f g (M T) hf hg hfnn hdom hL2 hnorm
  simpa [f,N] using hres
