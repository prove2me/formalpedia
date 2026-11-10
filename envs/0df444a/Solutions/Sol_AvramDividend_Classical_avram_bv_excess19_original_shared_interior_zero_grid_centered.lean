-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess19_original_shared_interior_zero_grid_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T20:21:17.739331+00:00
-- url     : https://prove2.me/submissions/85caf0f3-11da-4660-be71-e1770683df19

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_triangular_grid_compensator_L1_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess18_original_stopped_zero_contact_finite_grid_L1_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (hDstrat : IsDividendStrategy 𝓕 D)
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
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n i, u n i ≤ u n (i + 1))
    (r : (n : ℕ) → Fin (n + 1) → ℕ → ℝ≥0)
    (hsr : ∀ n (i : Fin (n + 1)) k, u n i.val < r n i k)
    (hrt : ∀ n (i : Fin (n + 1)) k, r n i k ≤ u n (i.val + 1))
    (hShort : ∀ n (i : Fin (n + 1)),
      Tendsto (fun k => r n i k - u n i.val) atTop (𝓝 0))
    (hLong : ∀ n (i : Fin (n + 1)),
      Tendsto (fun k => u n (i.val + 1) - r n i k)
        atTop (𝓝 (u n (i.val + 1) - u n i.val)))
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (v : (n : ℕ) → Fin (n + 1) → ℝ) :
    let Mpos : ℕ → Ω → ℝ := fun n ω =>
      let K : ℝ≥0 → Ω → ℝ := fun S ω' =>
        let τ : Ω → ℝ≥0 := fun ξ =>
          (min (ruinTime X x D ξ) (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2)
              p.1 ∈ Icc (a n) (b n)}
        let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if p.1 ∈ E ∧ p.2 < 0 then
            Real.exp (-(q * (p.1.1 : ℝ))) *
              (w (Function.leftLim
                (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2)
                  p.1.1 + p.2) -
               w (Function.leftLim
                (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2)
                  p.1.1))
          else 0
        let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ξ =>
          ((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ξ -
              Function.leftLim (fun z : ℝ≥0 => X.X z ξ) t ≠ 0}).map
            (fun t : ℝ≥0 => (t,
              X.X t ξ - Function.leftLim (fun z : ℝ≥0 => X.X z ξ) t)))
        (∫ p, H ((p.1, ω'), p.2) ∂(NX ω')) -
          (∫ t, ∫ z, H ((t, ω'), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map
              Real.toNNReal))
      Finset.sum (Finset.range (n + 1))
        (fun i => K (u n (i + 1)) ω - K (u n i) ω)
    let Mzero : ℕ → Ω → ℝ := fun n ω =>
      Finset.sum Finset.univ (fun i : Fin (n + 1) =>
        (if (u n i.val : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
                (u n i.val) = 0 then v n i else 0) *
        ((((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t,
            X.X t ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) t)))
          (Ioc (u n i.val) (u n (i.val + 1)) ×ˢ Iio (0 : ℝ))).toReal -
          (((u n (i.val + 1) - u n i.val : ℝ≥0) : ℝ≥0∞) *
            X.ν (Iio (0 : ℝ))).toReal))
    ∀ n, Integrable (fun ω => Mpos n ω + Mzero n ω) P ∧
      (∫ ω, Mpos n ω + Mzero n ω ∂P) = 0 := by
  classical
  dsimp only
  intro n
  have hPos :=
    (avram_bv_meas7_original_triangular_grid_compensator_L1_centered
      X hBV x C D hD w hw_cont hw_neg hw_smooth
      q hq hw_gen a b ha ha2 hab hBand u) n
  have hZero :=
    avram_bv_excess18_original_stopped_zero_contact_finite_grid_L1_mean_zero
      X x D hDstrat
      (fun i : Fin (n + 1) => u n i.val)
      (fun i : Fin (n + 1) => u n (i.val + 1))
      (fun i => hu n i.val) (r n)
      (hsr n) (hrt n) (hShort n) (hLong n)
      hFinite (v n)
  exact ⟨hPos.1.add hZero.1,
    by rw [integral_add hPos.1 hZero.1, hPos.2, hZero.2, add_zero]⟩
