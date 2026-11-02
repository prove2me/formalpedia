-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_source_count_nat_supported_summable_poisson_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:57:21.253235+00:00
-- url     : https://prove2.me/submissions/707c37d9-00ef-4b9e-9487-61e8127416e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_source_total_count_poisson_weighted_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical Real Finset
open scoped NNReal ENNReal BigOperators Nat
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Actual original BV jump count: filtration-measurable nat-supported proxy,
exact summable Poisson first-moment series, and same-path identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T) :
    ∃ F : Ω → ℝ≥0∞, Measurable[𝓕 T] F ∧
      (∀ᵐ ω ∂P,
        F ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) ∧
      (∀ᵐ ω ∂P, ∃ k : ℕ, F ω = (k : ℝ≥0∞)) ∧
      Summable (fun k : ℕ => (k : ℝ) *
        P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) ∧
      (∑' k : ℕ, (k : ℝ) *
        P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) =
        (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let J : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
  obtain ⟨F, hFm, hFae, hFLaw⟩ :=
    avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
      X hBV hFinite T hT grid hGrid hMesh hBound
  have hFmeas : Measurable F := hFm.mono (𝓕.le T) le_rfl
  have hN : ∀ᵐ ω ∂P, ∃ k : ℕ, F ω = (k : ℝ≥0∞) := by
    filter_upwards [hFae,
      avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
        X hBV hFinite] with ω hEq hfin
    let S : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Set.univ}
    have hS : S.Finite := by
      apply (hfin T).subset
      intro u ⟨huPos, _, huLe, huJump, _⟩
      exact ⟨huLe, huPos, huJump⟩
    refine ⟨S.ncard, ?_⟩
    have hJ := avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω 0 T (Set.univ : Set ℝ) MeasurableSet.univ
    change J ω = (S.encard : ℝ≥0∞) at hJ
    change F ω = J ω at hEq
    rw [hJ] at hEq
    exact hEq.trans (congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) hS.encard_eq_coe)
  let r : ℝ≥0 :=
    ⟨(T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal,
      mul_nonneg (NNReal.coe_nonneg T) ENNReal.toReal_nonneg⟩
  have hPMF (k : ℕ) :
      P.real {ω : Ω | F ω = (k : ℝ≥0∞)} =
      (poissonMeasure r).real {k} := by
    rw [hFLaw k, poissonMeasure_real_singleton]
    rfl
  have hmass :
      HasSum (fun n : ℕ => (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using
      hasSum_one_poissonMeasure r
  have hshift (n : ℕ) :
      ((n + 1 : ℕ) : ℝ) * (poissonMeasure r).real {n + 1} =
        (r : ℝ) * (poissonMeasure r).real {n} := by
    simp only [poissonMeasure_real_singleton, Nat.factorial_succ,
      Nat.cast_mul, pow_succ]
    have hf : ((n ! : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  have hExp : HasSum (fun n : ℕ =>
      (n : ℝ) * (poissonMeasure r).real {n}) (r : ℝ) := by
    apply (hasSum_nat_add_iff' 1).mp
    simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    simp_rw [hshift]
    simpa [mul_one] using hmass.mul_left (r : ℝ)
  have hSumm : Summable (fun k : ℕ =>
      (k : ℝ) * P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) := by
    have hSame : (fun k : ℕ =>
      (k : ℝ) * P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) =
      (fun k : ℕ => (k : ℝ) * (poissonMeasure r).real {k}) := by
      funext k
      rw [hPMF k]
    rw [hSame]
    exact hExp.summable
  obtain ⟨G, _hGmeas, hGae, hRealG⟩ :=
    avram_wave5_01_bv_actual_source_total_count_poisson_weighted_first_moment
      X hBV hFinite T hT grid hGrid hMesh hBound
  have hFGeq : ∀ᵐ ω ∂P, F ω = G ω := by
    filter_upwards [hFae, hGae] with ω hF hG
    exact hF.trans hG.symm
  have hReal :
      (∑' k : ℕ, (k : ℝ) *
        P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) =
        (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by
    calc
      _ = ∑' k : ℕ, (k : ℝ) *
          P.real {ω : Ω | G ω = (k : ℝ≥0∞)} := by
        apply tsum_congr
        intro k
        congr 1
        have hLevel : ∀ᵐ ω ∂P,
            (F ω = (k : ℝ≥0∞) ↔ G ω = (k : ℝ≥0∞)) := by
          filter_upwards [hFGeq] with ω hω
          rw [hω]
        exact congrArg ENNReal.toReal
          (measure_congr (Filter.eventuallyEq_set.mpr hLevel))
      _ = _ := hRealG
  exact ⟨F, hFm, hFae, hN, hSumm, hReal⟩
