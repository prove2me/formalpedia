-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_ruin_truncated_concrete_jump_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:04:48.12503+00:00
-- url     : https://prove2.me/submissions/c3570728-2766-4ef8-aa15-4debc284d70e

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_P2_rectangle_to_stopped_jump_zero_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The P2 original rectangle compensation bridge applies to the literal
integer-truncated ruin clock and its literal intrinsic source marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (n : ℕ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤
          ((τ p.1.2 : ℝ≥0) : ℝ≥0∞) then G p else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 ((n : ℝ≥0) : ℝ))).map
          Real.toNNReal))) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 ((n : ℝ≥0) : ℝ))).map
          Real.toNNReal))) ∂P) = 0 := by
  dsimp only
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hClock : (∀ ω, τ ω ≤ (n : ℝ≥0)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => (τ ω : WithTop ℝ≥0)) :=
    avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
      X x D hD n
  exact avram_p3_main_original_P2_rectangle_to_stopped_jump_zero_mean
    X hBV NX (by intro; rfl)
    (n : ℝ≥0) τ hClock.1 hClock.2
    x D hD w hw_cont hw_neg q hq
    a b L R ha ha2 hab hL hR hLip hWbound
    E hEm hEregion hν G (by intro; rfl) H rfl
