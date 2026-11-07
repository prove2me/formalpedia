-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_original_given_uniform_grid_intrinsic_compensator_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:26:23.552555+00:00
-- url     : https://prove2.me/submissions/4c5c1022-abb5-4c52-9720-d7094cd660f0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_physical_grid_compensator_auto
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uniform_physical_grid_prefix_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped X.ν compensated source is centred on a supplied uniform
grid, with no substitution of its process, dividends or active cell times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0)
    (huWidth : ∀ n i, i < n + 1 →
      (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2)) :
    ∀ n : ℕ,
      let M : ℝ≥0 → Ω → ℝ := fun S ω =>
        let τ : Ω → ℝ≥0 := fun ω' =>
          (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
        let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if p.1 ∈ E ∧ p.2 < 0 then
            Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
             w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
          else 0
        let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
          ((Measure.count.restrict
            {v : ℝ≥0 | 0 < v ∧
              X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map
            (fun v : ℝ≥0 => (v,
              X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      Integrable (fun ω => Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω)) P ∧
      (∫ ω, Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω) ∂P) = 0 := by
  obtain ⟨v, hv0, _hvEnd, _hvMono, hvWidth, hvM⟩ :=
    avram_bv_meas7_original_uniform_physical_grid_compensator_auto
      X hBV x C D hD w hw_cont hw_neg hw_smooth q hq hw_gen
      a b ha ha2 hab hBand T hT
  have hSame (n i : ℕ) (hi : i ≤ n + 1) : u n i = v n i :=
    avram_bv_meas7_uniform_physical_grid_prefix_unique
      T u v hu0 hv0 huWidth hvWidth n i hi
  intro n
  let M : ℝ≥0 → Ω → ℝ := fun S ω =>
    let τ : Ω → ℝ≥0 := fun ω' =>
      (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
      ((Measure.count.restrict
        {v : ℝ≥0 | 0 < v ∧
          X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
    (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
  change Integrable (fun ω => Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω)) P ∧
    (∫ ω, Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω) ∂P) = 0
  have hOld : Integrable (fun ω => Finset.sum (Finset.range (n + 1))
        (fun i => M (v n (i + 1)) ω - M (v n i) ω)) P ∧
    (∫ ω, Finset.sum (Finset.range (n + 1))
        (fun i => M (v n (i + 1)) ω - M (v n i) ω) ∂P) = 0 := by
    exact hvM n
  have hEqual : (fun ω : Ω => Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω)) =
    (fun ω : Ω => Finset.sum (Finset.range (n + 1))
        (fun i => M (v n (i + 1)) ω - M (v n i) ω)) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    rw [hSame n i (Nat.le_of_lt hi'),
        hSame n (i + 1) (Nat.succ_le_of_lt hi')]
  simpa only [hEqual] using hOld