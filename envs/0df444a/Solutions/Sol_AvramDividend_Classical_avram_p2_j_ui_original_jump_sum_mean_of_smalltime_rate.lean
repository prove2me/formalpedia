-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_jump_sum_mean_of_smalltime_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:37:25.504411+00:00
-- url     : https://prove2.me/submissions/76302839-abb6-4574-9668-e98574c6d7a0

import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal BigOperators

/-- The actual original finite jump sum inherits its marginal rate via direct stationary cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (L : ℝ)
    (hRate : Tendsto
      (fun h : ℝ => (∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          g ((X.X u ω - X.X 0 ω) -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F, g ((X.X u ω - X.X 0 ω) -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u)) ∧
      (∫ ω, J ω ∂P) = (T : ℝ) * L := by
  obtain ⟨J, hJ, hRep, hL1, hMean⟩ :=
    avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
      P X T hT g hg hc hneg
  have hBase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hMesh : Tendsto (fun n : ℕ => (T : ℝ) / ((n : ℝ) + 1))
      atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero, one_div, div_eq_mul_inv, one_mul] using
        hBase.const_mul (T : ℝ)
    · apply Filter.Eventually.of_forall
      intro n
      change 0 < (T : ℝ) / ((n : ℝ) + 1)
      exact div_pos (by exact_mod_cast hT) (by positivity)
  have hProd := Filter.Tendsto.const_mul (T : ℝ) (hRate.comp hMesh)
  have hSmall : Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      ∫ ω, g (X.X (Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω) ∂P)
      atTop (nhds ((T : ℝ) * L)) := by
    convert hProd using 1
    ext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hTR : (T : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hT)
    simp only [Function.comp_def]
    field_simp [hTR, hn]
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
  have hGrid (n : ℕ) :
      (∫ ω, ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
           X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
      ((n : ℝ) + 1) *
        (∫ ω, g (X.X (T / ((n : ℝ≥0) + 1)) ω) ∂P) := by
    let δ : ℝ≥0 := T / ((n : ℝ≥0) + 1)
    have hXm : Measurable (X.X δ) :=
      (X.adapted _).mono (𝓕.le _) le_rfl
    have hIntδ : Integrable (fun ω => g (X.X δ ω)) P := by
      apply Integrable.of_bound ((hg.measurable.comp hXm).aestronglyMeasurable) C
      exact Filter.Eventually.of_forall (fun ω => hC (X.X δ ω))
    have hLaw (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
        IdentDistrib
          (fun ω => g (X.X ((↑(i + 1) : ℝ≥0) * δ) ω -
                         X.X ((i : ℝ≥0) * δ) ω))
          (fun ω => g (X.X δ ω)) P P := by
      have hTime : (i : ℝ≥0) * δ ≤ ((i + 1 : ℕ) : ℝ≥0) * δ := by
        gcongr
        exact Nat.le_succ i
      have hDelta : ((i + 1 : ℕ) : ℝ≥0) * δ - (i : ℝ≥0) * δ = δ := by
        have hCast : ((i + 1 : ℕ) : ℝ≥0) = (i : ℝ≥0) + 1 := by norm_cast
        rw [hCast, add_mul, one_mul, add_tsub_cancel_left]
      simpa only [Function.comp_def, hDelta] using
        (X.stationaryIncrements ((i : ℝ≥0) * δ)
          (((i + 1 : ℕ) : ℝ≥0) * δ) hTime).comp hg.measurable
    calc
      (∫ ω, ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * δ) ω - X.X ((i : ℝ≥0) * δ) ω) ∂P) =
          ∑ i ∈ Finset.range (n + 1),
            ∫ ω, g (X.X ((↑(i + 1) : ℝ≥0) * δ) ω -
               X.X ((i : ℝ≥0) * δ) ω) ∂P := by
        apply integral_finset_sum
        intro i hi
        exact (hLaw i hi).integrable_iff.mpr hIntδ
      _ = ∑ i ∈ Finset.range (n + 1), ∫ ω, g (X.X δ ω) ∂P := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hLaw i hi).integral_eq
      _ = ((n : ℝ) + 1) * (∫ ω, g (X.X δ ω) ∂P) := by
        simp [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
  have hCoe (n : ℕ) :
      Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      T / ((n : ℝ≥0) + 1) := by
    have hden : ((n : ℝ) + 1) = (((n : ℝ≥0) + 1) : ℝ) := by norm_cast
    rw [hden, Real.toNNReal_div (NNReal.coe_nonneg T)]
    simp
  have hLimit : Tendsto (fun n : ℕ => ∫ ω,
      ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
           X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P)
      atTop (nhds ((T : ℝ) * L)) := by
    have hFunction :
        (fun n : ℕ => ∫ ω,
          ∑ i ∈ Finset.range (n + 1),
            g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
               X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
        (fun n : ℕ => ((n : ℝ) + 1) *
          ∫ ω, g (X.X (Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω) ∂P) := by
      funext n
      rw [hCoe n]
      exact hGrid n
    rw [hFunction]
    exact hSmall
  exact ⟨J, hJ, hRep, tendsto_nhds_unique hMean hLimit⟩
