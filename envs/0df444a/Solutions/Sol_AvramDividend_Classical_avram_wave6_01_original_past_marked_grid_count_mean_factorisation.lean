-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_mean_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:57:06.343011+00:00
-- url     : https://prove2.me/submissions/bc781365-f03c-461e-974e-5d5f6ae31fc5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Genuine source predictable-past finite marked-increment grid mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0)
    (n : ℕ) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω,
      (A.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
      (∑ i ∈ Finset.range n,
        ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ∂P) =
    P A * (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) := by
  classical
  haveI := X.isProbability
  let S : Finset ℕ := Finset.range n
  let E : ℕ → Set Ω := fun i =>
    {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}
  let Y : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω
  let Z : Ω → ℝ≥0∞ := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hXm (u : ℝ≥0) : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hE (i : ℕ) : MeasurableSet (E i) :=
    hB.preimage ((hXm _).sub (hXm _))
  have hY (i : ℕ) : Measurable (Y i) :=
    measurable_const.indicator (hE i)
  have hAambient : MeasurableSet A := (𝓕.le s) A hA
  have hZ : Measurable Z := measurable_const.indicator hAambient
  have hProd (i : ℕ) :
      (fun ω : Ω => Z ω * Y i ω) =
        (A ∩ E i).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hi : ω ∈ E i <;>
      simp [Y, Z, ha, hi]
  have hProdMean (i : ℕ) :
      (∫⁻ ω, Z ω * Y i ω ∂P) = P (A ∩ E i) := by
    calc
      (∫⁻ ω, Z ω * Y i ω ∂P) =
        ∫⁻ ω, (A ∩ E i).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            exact congrArg
              (fun f : Ω → ℝ≥0∞ => ∫⁻ ω, f ω ∂P) (hProd i)
      _ = P (A ∩ E i) :=
        MeasureTheory.lintegral_indicator_one (hAambient.inter (hE i))
  have hFactor (i : ℕ) :
      P (A ∩ E i) = P A * P (E i) := by
    have hsi : s ≤ t i :=
      hst.trans (ht (Nat.zero_le i))
    have hAi : MeasurableSet[𝓕 (t i)] A :=
      (𝓕.mono hsi) A hA
    exact chat04_past_event_next_levy_increment_measure_product
      X (t i) (t (i + 1)) (ht (Nat.le_succ i))
        A hAi B hB
  change (∫⁻ ω, Z ω * (∑ i ∈ S, Y i ω) ∂P) =
    P A * ∑ i ∈ S, P (E i)
  calc
    (∫⁻ ω, Z ω * (∑ i ∈ S, Y i ω) ∂P) =
        ∫⁻ ω, ∑ i ∈ S, Z ω * Y i ω ∂P := by
          exact congrArg
            (fun f : Ω → ℝ≥0∞ => ∫⁻ ω, f ω ∂P)
            (funext (fun ω => by simp only [Finset.mul_sum]))
    _ = ∑ i ∈ S, ∫⁻ ω, Z ω * Y i ω ∂P := by
      apply MeasureTheory.lintegral_finset_sum
      intro i hi
      exact hZ.mul (hY i)
    _ = ∑ i ∈ S, P (A ∩ E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hProdMean i
    _ = ∑ i ∈ S, P A * P (E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hFactor i
    _ = P A * ∑ i ∈ S, P (E i) := by
      rw [Finset.mul_sum]
