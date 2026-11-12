-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb27_original_finitecap_quadratic_grid_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:34:01.931395+00:00
-- url     : https://prove2.me/submissions/fb554de6-5c5e-4a6c-98e5-7375b096c98d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
/-- Original same-path compensated quadratic Gaussian grid is event-integrable. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq :
0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal
y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x)
(hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t =
0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω =
(min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (hσstop : ∀ k,
IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ σ k ω)
(δ : ℝ) (hδ : 0 < δ) (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω) (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∀ (j m : ℕ),
      let Q : Ω → ℝ := fun ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
        let H : ℕ → Ω → ℝ := fun i η => if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
        (Finset.range (m + 1)).sum (fun i => H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      IntegrableOn Q A P := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA j m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : ℕ → Ω → ℝ := fun i ω =>
    x + X.X (s i) ω - rightLimit D (s i) ω
  let Z : ℕ → Ω → ℝ := fun i ω =>
    X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  let H : ℕ → Ω → ℝ := fun i ω =>
    if s i < ρ ω then (1 / 2 : ℝ) *
      Real.exp (-(q * (s i : ℝ))) *
      (if Y i ω ∈ Icc a b then iteratedDeriv 2 w (Y i ω) else 0)
    else 0
  let Q : Ω → ℝ := fun ω => (Finset.range (m + 1)).sum
    (fun i => H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
  change IntegrableOn Q A P
  have ha : 0 < a := by dsimp [a]; linarith
  have hCpos : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    change IsOpen (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' Iio C)
    exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    have hf : (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) < 1 := by
      apply (div_lt_one (by positivity)).2
      exact_mod_cast Nat.lt_succ_self (j + 1)
    have hb : b < C.toReal := by
      dsimp [b]
      nlinarith [mul_lt_mul_of_pos_left hf hCpos]
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    exact ⟨hy0,
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy0) hFiniteCap).2
        (lt_of_le_of_lt hy.2 hb)⟩
  have hHess :=
    avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
      w C hw_smooth
  obtain ⟨KG, KH, hKG, hKH, hGB, hHB⟩ :=
    avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
      X hBV hν q (le_of_lt hq) C w hw_smooth hOpen a b hBand
  have hCell (i : ℕ) :
      Integrable (fun ω => H i ω *
        (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2)) P := by
    let t : ℝ≥0 := s i
    have hY : Measurable[𝓕.rightCont t] (Y i) := by
      have hXm := (X.adapted t).mono (𝓕.le_rightCont t) le_rfl
      have hDm := (dividendStrategy_rightLimit_adapted_rightCont D hD.1.1) t
      exact (measurable_const.add hXm).sub hDm
    have hMask : MeasurableSet[𝓕.rightCont t] {ω : Ω | t < ρ ω} := by
      have he : {ω : Ω | t < ρ ω} =
          {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ t}ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
          WithTop.coe_le_coe, not_le]
      rw [he]
      exact (hρstop t).compl
    have hHessian :
        Measurable (fun y : ℝ =>
          if y ∈ Icc a b then iteratedDeriv 2 w y else 0) := by
      have heq : (fun y : ℝ =>
          if y ∈ Icc a b then iteratedDeriv 2 w y else 0) =
          (fun y => if y ∈ Icc a b then
            (if 0 < y ∧ ENNReal.ofReal y < C
             then iteratedDeriv 2 w y else 0) else 0) := by
        funext y
        by_cases hy : y ∈ Icc a b
        · obtain ⟨hy0, hyC⟩ := hBand hy
          simp [hy, hy0, hyC]
        · simp [hy]
      rw [heq]
      exact Measurable.ite measurableSet_Icc hHess measurable_const
    have hHm : Measurable[𝓕.rightCont t] (H i) := by
      change Measurable[𝓕.rightCont t] (fun ω =>
        if t < ρ ω then (1 / 2 : ℝ) *
          Real.exp (-(q * (t : ℝ))) *
          (if Y i ω ∈ Icc a b then iteratedDeriv 2 w (Y i ω) else 0)
        else 0)
      exact Measurable.ite hMask
        ((measurable_const.mul measurable_const).mul
          (hHessian.comp hY)) measurable_const
    have hHb : ∀ ω, |H i ω| ≤ KH := by
      intro ω
      by_cases hs : t < ρ ω
      · by_cases hy : Y i ω ∈ Icc a b
        · have hh := hHB t (Y i ω) hy
          have hhalf :
              |(1 / 2 : ℝ) * (Real.exp (-(q * (t : ℝ))) *
                iteratedDeriv 2 w (Y i ω))| ≤ KH := by
            rw [abs_mul, abs_of_nonneg
              (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            nlinarith
          simpa only [H, t, if_pos hs, if_pos hy] using
            (show |(1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) *
                iteratedDeriv 2 w (Y i ω)| ≤ KH by
              convert hhalf using 1 <;> ring)
        · simpa only [H, t, if_pos hs, if_neg hy,
            mul_zero, abs_zero] using hKH
      · simp [H, t, hs, hKH]
    have hQ := avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
      X hν t (t + Δ) (le_add_of_nonneg_right bot_le)
    have hQI : Integrable (fun ω =>
        Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2) P := by
      simpa only [Z, t, NNReal.coe_add, add_sub_cancel_left] using hQ.1
    have hHg : Measurable (H i) :=
      hHm.mono (𝓕.rightCont.le t) le_rfl
    apply hQI.bdd_mul hHg.stronglyMeasurable.aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs] using hHb ω
  have hAll : Integrable Q P := by
    apply integrable_finset_sum
    intro i hi
    exact hCell i
  exact hAll.integrableOn
