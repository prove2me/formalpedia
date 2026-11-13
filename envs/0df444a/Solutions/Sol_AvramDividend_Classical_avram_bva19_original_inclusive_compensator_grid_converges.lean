-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva19_original_inclusive_compensator_grid_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:44:00.869216+00:00
-- url     : https://prove2.me/submissions/2986c8bb-9c5a-419f-a816-3a2b8dbacc6d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_real_time_stopped_mark_floor_DCT
import Theorems.Thm_AvramDividend_Classical_avram_bvb27a_original_finite_mark_grid_to_real_floor
import Theorems.Thm_AvramDividend_Classical_avram_bvb27b_original_stopped_mark_compensator_real_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (hMassPos : 0 < X.ν (Iio (0 : ℝ))) (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn
        (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s)
    (ω : Ω) (hRuinNonzero : ruinTime X x D ω ≠ 0) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let K : ℕ → Ω → ℝ := fun n ω =>
      (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
    let A : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      ∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 ≤ Z i ∧ ENNReal.ofReal (Z i) ≤ C then
          (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
            (w (Z i + z) - w (Z i)) ∂X.ν) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
    (∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift) →
      (NX ω) (Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)) = 0 →
      Tendsto (fun n => K n ω - A n ω) atTop (𝓝 0) := by
  intro δ S U H NX K A hSource hMarks
  let Uo : ℝ≥0 → ℝ := fun t => U t ω
  let ψ : ℝ → ℝ := fun b =>
    ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
  let rate : ℝ≥0 → ℝ := fun t =>
    Real.exp (-(q * (t : ℝ))) * ψ (Uo t)
  let F : ℕ → ℝ → ℝ := fun n r =>
    if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
      let i : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ Uo (u n i) ∧ ENNReal.ofReal (Uo (u n i)) ≤ C
      then rate (u n i) else 0
    else 0
  let G : ℕ → ℝ → ℝ := fun n r =>
    let t : ℝ≥0 := Real.toNNReal r
    if 0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
       (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
       0 ≤ Uo t ∧ ENNReal.ofReal (Uo t) ≤ C
    then rate t else 0
  obtain ⟨hMeas, hDCT⟩ :=
    avram_bvb24_original_real_time_stopped_mark_floor_DCT
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x hx hxc D hD T hT u hgrid hmono huniform hFinite hActivity
      hMassPos hKernel ω hRuinNonzero hSource
  change Tendsto (fun n =>
    (∫ r in Icc (0 : ℝ) T, G n r) -
    (∫ r in Icc (0 : ℝ) T, F n r))
    atTop (𝓝 (0 : ℝ)) at hDCT
  have hK (n : ℕ) :
      K n ω = ∫ r in Icc (0 : ℝ) T, G n r := by
    have hb :=
      (avram_bvb27b_original_stopped_mark_compensator_real_clock
         X C (ruinTime X x D ω) Uo w q T n)
        (by simpa only [and_assoc] using hMeas n)
    change K n ω = ∫ r in Icc (0 : ℝ) T, G n r at hb
    exact hb
  have hA (n : ℕ) :
      A n ω = ∫ r in Icc (0 : ℝ) T, F n r := by
    have hb :=
      avram_bvb27a_original_finite_mark_grid_to_real_floor
        X x q T hT w C D u huniform n ω
    change A n ω = ∫ r in Icc (0 : ℝ) T, F n r at hb
    exact hb
  simpa only [hK, hA] using hDCT
