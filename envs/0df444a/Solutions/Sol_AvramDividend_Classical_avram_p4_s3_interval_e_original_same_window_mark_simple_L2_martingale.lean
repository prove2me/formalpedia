-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_e_original_same_window_mark_simple_L2_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:27:15.546195+00:00
-- url     : https://prove2.me/submissions/6b790efa-daea-4d25-9095-5594a08797f7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite mark-simple predictable sum of genuine same-time original compensated cells is L² and centred. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ι → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 s] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (F : Finset ι) :
    let Z : ι → Ω → ℝ := fun i ω =>
      H i ω * (((((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)).toReal) -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    MemLp (∑ i ∈ F, Z i) 2 P ∧
    P[(∑ i ∈ F, Z i) | 𝓕 s] =ᵐ[P] (0 : Ω → ℝ) := by
  classical
  let Z : ι → Ω → ℝ := fun i ω =>
    H i ω * (((((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B i)).toReal) -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
  change MemLp (∑ i ∈ F, Z i) 2 P ∧
    P[(∑ i ∈ F, Z i) | 𝓕 s] =ᵐ[P] (0 : Ω → ℝ)
  have hCell (i : ι) :
      MemLp (Z i) 2 P ∧
        P[Z i | 𝓕 s] =ᵐ[P] (0 : Ω → ℝ) :=
    avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto
      X T cut s t hst htT ε hε (B i) (hB i) (hBand i)
        (hCut i) (H i) (hH i) (hHL2 i) L (hBound i)
  have hIntegrable (i : ι) : Integrable (Z i) P :=
    (hCell i).1.integrable (by norm_num)
  have hSumL2 (S : Finset ι) : MemLp (∑ i ∈ S, Z i) 2 P := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a R ha ih =>
      simpa only [Finset.sum_insert ha] using ((hCell a).1.add ih)
  have hZero :
      (∑ i ∈ F, P[Z i | 𝓕 s]) =ᵐ[P] (0 : Ω → ℝ) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      filter_upwards [(hCell a).2, ih] with ω hA hS
      calc
        (∑ i ∈ insert a S, P[Z i | 𝓕 s]) ω =
            P[Z a | 𝓕 s] ω + (∑ i ∈ S, P[Z i | 𝓕 s]) ω := by
              simp only [Finset.sum_insert ha, Pi.add_apply]
        _ = 0 := by
          rw [hA, hS]
          simp
  constructor
  · exact hSumL2 F
  · exact (condExp_finset_sum (s := F) (f := Z)
      (by intro i hi; exact hIntegrable i) (𝓕 s)).trans hZero
