-- Prove2me | solution 1 for Equidistribution.exists_continuous_sandwich_indicator
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:56:09.84486+00:00
-- url     : https://prove2.me/submissions/fe6170f8-1364-4f16-8199-5a90a7162c9b

import Mathlib

open MeasureTheory

set_option autoImplicit false

open Set

theorem solution {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    (U : Set X) (hU : IsOpen U) (h0 : μ (frontier U) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ u₁ u₂ : C(X, ℝ),
      (∀ x, 0 ≤ u₁ x ∧ u₁ x ≤ U.indicator (fun _ => (1 : ℝ)) x ∧
        U.indicator (fun _ => (1 : ℝ)) x ≤ u₂ x ∧ u₂ x ≤ 1) ∧
      ∫ x, (u₂ x - u₁ x) ∂μ < ε := by
  have : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  have hδ : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  -- A compact set inside `U` and an open set around its closure, both of nearly the same mass.
  obtain ⟨K, hKU, hK, hKμ⟩ := hU.measurableSet.exists_isCompact_lt_add (measure_ne_top μ U) hδ
  obtain ⟨V, hV, hVo, hVμ⟩ := (closure U).exists_isOpen_lt_add (measure_ne_top μ _) hδ
  have hcl : μ (closure U) ≤ μ U := by
    rw [closure_eq_self_union_frontier]
    exact (measure_union_le _ _).trans (by rw [h0, add_zero])
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
    hK.isClosed (disjoint_compl_left_iff_subset.mpr hKU)
  obtain ⟨g, hg0, hg1, hg01⟩ := exists_continuous_zero_one_of_isClosed hVo.isClosed_compl
    isClosed_closure (disjoint_compl_left_iff_subset.mpr hV)
  refine ⟨f, g, fun x => ?_, ?_⟩
  · by_cases hx : x ∈ U
    · have hgx : g x = 1 := hg1 (subset_closure hx)
      rw [indicator_of_mem hx, hgx]
      exact ⟨(hf01 x).1, (hf01 x).2, le_rfl, le_rfl⟩
    · have hfx : f x = 0 := hf0 hx
      rw [indicator_of_notMem hx, hfx]
      exact ⟨le_rfl, le_rfl, (hg01 x).1, (hg01 x).2⟩
  · have hKV : K ⊆ V := hKU.trans (subset_closure.trans hV)
    have hmeas : MeasurableSet (V \ K) := hVo.measurableSet.diff hK.measurableSet
    have hpt (x : X) : g x - f x ≤ (V \ K).indicator (fun _ => (1 : ℝ)) x := by
      by_cases hxK : x ∈ K
      · have hfx : f x = 1 := hf1 hxK
        rw [indicator_of_notMem (show x ∉ V \ K from fun h => h.2 hxK), hfx]
        linarith [(hg01 x).2]
      · by_cases hxV : x ∈ V
        · rw [indicator_of_mem (show x ∈ V \ K from ⟨hxV, hxK⟩)]
          linarith [(hg01 x).2, (hf01 x).1]
        · have hgx : g x = 0 := hg0 hxV
          have hfx : f x = 0 := hf0 fun h => hxV (hV (subset_closure h))
          rw [indicator_of_notMem (show x ∉ V \ K from fun h => hxV h.1), hgx, hfx, sub_zero]
    have hint : Integrable (fun x => g x - f x) μ :=
      (g.continuous.sub f.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hmass : μ (V \ K) < ENNReal.ofReal ε := by
      rw [measure_sdiff hKV hK.measurableSet.nullMeasurableSet (measure_ne_top μ K)]
      refine ENNReal.sub_lt_of_lt_add (measure_mono hKV) ?_
      calc μ V < μ (closure U) + ENNReal.ofReal (ε / 2) := hVμ
        _ ≤ μ K + ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (hcl.trans hKμ.le) le_rfl
        _ = ENNReal.ofReal ε + μ K := by
          rw [add_assoc, ← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves,
            add_comm]
    calc ∫ x, (g x - f x) ∂μ ≤ ∫ x, (V \ K).indicator (fun _ => (1 : ℝ)) x ∂μ :=
          integral_mono hint ((integrable_const 1).indicator hmeas) hpt
      _ = μ.real (V \ K) := by rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
      _ < ε := ENNReal.toReal_lt_of_lt_ofReal hmass
