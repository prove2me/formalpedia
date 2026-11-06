-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_stopped_finite_mark_family_bounded_auto_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:31:41.208428+00:00
-- url     : https://prove2.me/submissions/388b1320-f5c1-401b-b75e-563da8e0b8fc

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- On the original physical stopped grid, bounded predictable marked coefficients supply L² automatically. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε)
    (C : ι → ℕ → Set ℝ)
    (hC : ∀ j i, MeasurableSet (C j i))
    (hBand : ∀ j i, C j i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ j i, C j i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : ∀ j i, X.ν (C j i) < ⊤)
    (N : ι → ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j i, N j i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C j i))
    (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[𝓕.rightCont (grid i)] (H j i))
    (L : ι → ℝ) (hBound : ∀ j i ω, |H j i ω| ≤ L j)
    (n : ℕ) (F : Finset ι) :
    let Z : ι → Ω → ℝ := fun j ω =>
      ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H j i ω) *
          ((N j i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C j i)).toReal)
    MemLp (fun ω => ∑ j ∈ F, Z j ω) 2 P ∧
      (∫ ω, ∑ j ∈ F, Z j ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hHL2 (j : ι) (i : ℕ) : MemLp (H j i) 2 P := by
    have hGlobalSM : StronglyMeasurable (H j i) :=
      (hH j i).mono (𝓕.rightCont.le (grid i))
    exact
      MemLp.of_bound hGlobalSM.aestronglyMeasurable (L j)
        (Filter.Eventually.of_forall (fun ω => by
          simpa only [Real.norm_eq_abs] using hBound j i ω))
  exact
    avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
      X T cut τ hτstop grid hGrid hTime ε hε
      C hC hBand hCut hν N hActual H hH hHL2 L hBound n F
