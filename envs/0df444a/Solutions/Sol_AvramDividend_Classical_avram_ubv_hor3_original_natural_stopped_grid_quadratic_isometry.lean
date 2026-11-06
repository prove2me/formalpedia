-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_natural_stopped_grid_quadratic_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:16:19.63897+00:00
-- url     : https://prove2.me/submissions/d68586ae-cc84-4cff-9a74-eaececab9a38

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_natural_clock_predictable_grid_mask
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_rightcont_physical_grid_isometry_adapted_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

/-- Actual clipped-ruin stopped negative-band quadratic isometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hFinite : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ i ω, |H i ω| ≤ L)
    (hNEnd : ∀ i, StronglyMeasurable[𝓕.rightCont (grid (i + 1))]
      (fun ω => (N i ω).toReal))
    (hSecond : ∀ i,
      P[(fun ω => ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) ^ 2)
      | 𝓕.rightCont (grid i)] =ᵐ[P]
      (fun _ => (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (B i)).toReal))
    (k : ℕ) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      (∫ ω, (∑ i ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
         then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (B i)).toReal)) ^ 2 ∂P) =
      ∑ i ∈ Finset.range k,
        ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) *
        ∫ ω, (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) ^ 2 ∂P := by
  obtain ⟨τ, hτEq, hMaskMeas⟩ :=
    avram_ubv_hor3_original_natural_clock_predictable_grid_mask
      X x Cap D hD n grid H hH
  let F : ℕ → Ω → ℝ := fun i ω =>
    if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
    then 0 else H i ω
  let r : ℕ → ℝ := fun i =>
    (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
  let Di : ℕ → Ω → ℝ := fun i ω => F i ω * ((N i ω).toReal - r i)
  have hFL2 : ∀ i, MemLp (F i) 2 P := by
    intro i
    have hFGlobal : StronglyMeasurable (F i) :=
      (hMaskMeas i).mono ((𝓕.rightCont).le (grid i))
    apply (hHL2 i).of_le hFGlobal.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
            then (0 : ℝ) else H i ω)‖ ≤ ‖H i ω‖
    by_cases h : (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
    · simpa only [if_pos h, norm_zero] using (norm_nonneg (H i ω))
    · simp only [if_neg h, le_refl]
  have hFBnd : ∀ i ω, |F i ω| ≤ L := by
    intro i ω
    by_cases h : (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
    · change |(if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω)| ≤ L
      simpa only [if_pos h, abs_zero] using hL
    · change |(if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω)| ≤ L
      simpa only [if_neg h] using hBound i ω
  have hIso :=
    avram_p4_s3_run1640_original_rightcont_physical_grid_isometry_adapted_auto
      X T cut grid hGrid hTime ε hε B hB hBand hCut hFinite
      N hActual r (by intro i; rfl) F Di (by intro i ω; rfl)
      (by simpa only [F] using hMaskMeas) hFL2 L hFBnd
      hNEnd (by simpa only [r] using hSecond) k
  exact ⟨τ, hτEq, by simpa only [Di, F, r] using hIso⟩
