-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_C1_partition_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:55:57.021768+00:00
-- url     : https://prove2.me/submissions/815ef1a0-0950-4ac2-8dd8-a0a66ad1969f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/--
On every stopped finite partition of the original BV source path,
the C1 derivative-weighted residual variation beyond the actual
source jumps has nonpositive signed contribution.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hgrad : ∀ i : Fin n,
          0 ≤ deriv w (riskProcess X x D (u i) ω)),
        ∃ r : Fin n → ℝ≥0∞,
          (∀ i : Fin n,
            (∑' (v : ℝ≥0),
              if 0 < v ∧ v ∈ Ioc (u i) (u (i + 1)) then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0) + r i =
              F.measure (Ioc (u i) (u (i + 1)))) ∧
          (∑ i : Fin n,
            -(deriv w (riskProcess X x D (u i) ω)) *
              (r i).toReal) ≤ 0 := by
  filter_upwards
    [avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets X hBV]
    with ω hω
  obtain ⟨F, hF, hdom⟩ := hω
  refine ⟨F, hF, ?_⟩
  intro τ u hu n hstop hgrad
  classical
  have hex (i : Fin n) : ∃ r : ℝ≥0∞,
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ∈ Ioc (u i) (u (i + 1)) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0) + r =
        F.measure (Ioc (u i) (u (i + 1))) := by
    let mass : ℝ≥0∞ :=
      ∑' (v : ℝ≥0),
        if 0 < v ∧ v ∈ Ioc (u i) (u (i + 1)) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0
    have hle : mass ≤ F.measure (Ioc (u i) (u (i + 1))) := by
      convert (hdom (Ioc (u i) (u (i + 1))) measurableSet_Ioc) using 1
      dsimp [mass]
      apply tsum_congr
      intro v
      by_cases hv : 0 < v ∧ v ∈ Ioc (u i) (u (i + 1))
      · simp [hv]
      · simp [hv]
    refine ⟨F.measure (Ioc (u i) (u (i + 1))) - mass, ?_⟩
    change mass + (F.measure (Ioc (u i) (u (i + 1))) - mass) =
      F.measure (Ioc (u i) (u (i + 1)))
    rw [add_comm]
    exact tsub_add_cancel_of_le hle
  choose r hr using hex
  refine ⟨r, hr, ?_⟩
  apply Finset.sum_nonpos
  intro i hi
  have hproduct : 0 ≤
      deriv w (riskProcess X x D (u i) ω) * (r i).toReal :=
    mul_nonneg (hgrad i) ENNReal.toReal_nonneg
  nlinarith only [hproduct]
