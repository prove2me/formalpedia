-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:42:01.383829+00:00
-- url     : https://prove2.me/submissions/0204d44a-56ab-41ea-ac04-d38af6eb25f9

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
/-- The finite-cap compact-mask Gaussian grid is centred on every initial event. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ) (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω) (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∀ (N : ℕ → ℕ),
        let Δ : ℕ → ℝ≥0 := fun j => (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
        let a : ℝ := δ / 2
        let b : ℕ → ℝ := fun j => C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → ℕ → Ω → ℝ := fun j i ω => x + X.X (s j i) ω - rightLimit D (s j i) ω
        let Z : ℕ → ℕ → Ω → ℝ := fun j i ω => X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
        let G : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω) else 1) else 0
        let H : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j) then iteratedDeriv 2 w (Y j i ω) else 0) else 0
        let M : ℕ → Ω → ℝ := fun j ω => (Finset.range (N j + 1)).sum (fun i => G j i ω * Z j i ω + H j i ω * (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
        (∀ j, IntegrableOn (M j) A P) ∧ (∀ j, (∫ ω in A, M j ω ∂P) = 0) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA N
  letI : IsProbabilityMeasure P := X.isProbability
  let Δ : ℕ → ℝ≥0 := fun j => (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
  let a : ℝ := δ / 2
  let b : ℕ → ℝ := fun j => C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : ℕ → ℕ → Ω → ℝ := fun j i ω => x + X.X (s j i) ω - rightLimit D (s j i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun j i ω => X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
  let G : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω) else 1) else 0
  let H : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j) then iteratedDeriv 2 w (Y j i ω) else 0) else 0
  let Q : ℕ → ℕ → Ω → ℝ := fun j i ω => Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2
  let F : ℕ → ℕ → Ω → ℝ := fun j i ω => G j i ω * Z j i ω + H j i ω * Q j i ω
  let M : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range (N j + 1), F j i ω
  change (∀ j, IntegrableOn (M j) A P) ∧ (∀ j, (∫ ω in A, M j ω ∂P) = 0)
  have ha : 0 < a := by dsimp [a]; linarith
  have hCpos : 0 < C.toReal := ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by change IsOpen (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' Iio C) ; exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hBand (j : ℕ) : Icc a (b j) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    have hf : (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) < 1 := by apply (div_lt_one (by positivity)).2 ; exact_mod_cast Nat.lt_succ_self (j + 1)
    have hb : b j < C.toReal := by dsimp [b] ; nlinarith [mul_lt_mul_of_pos_left hf hCpos]
    intro y hy ; have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    exact ⟨hy0, (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy0) hFiniteCap).2 (lt_of_le_of_lt hy.2 hb)⟩
  have hGrad := avram_wave4_04b_measurable_cap_interior_deriv_zero_extension w C hw_smooth
  have hHess := avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension w C hw_smooth
  have hWeighted (t : ℝ≥0) (U V : Ω → ℝ) (c : ℝ) (hU : Measurable[𝓕.rightCont t] U) (hBound : ∀ ω, |U ω| ≤ c) (hVI : Integrable V P) (hCE : P[V | 𝓕.rightCont t] =ᵐ[P] fun _ => (0 : ℝ)) : Integrable (fun ω => U ω * V ω) P ∧ (∫ ω, U ω * V ω ∂P) = 0 := by
    have hUg : Measurable U := hU.mono (𝓕.rightCont.le t) le_rfl
    have hUV : Integrable (fun ω => U ω * V ω) P := by apply hVI.bdd_mul hUg.stronglyMeasurable.aestronglyMeasurable ; filter_upwards [] with ω ; simpa only [Real.norm_eq_abs] using hBound ω
    refine ⟨hUV, ?_⟩
    have hpull := condExp_mul_of_stronglyMeasurable_left hU.stronglyMeasurable hUV hVI
    calc
      (∫ ω, U ω * V ω ∂P) = (∫ ω, P[(fun ω => U ω * V ω) | 𝓕.rightCont t] ω ∂P) := by
            symm ; exact integral_condExp (𝓕.rightCont.le t)
      _ = (∫ ω, U ω * P[V | 𝓕.rightCont t] ω ∂P) := integral_congr_ae hpull
      _ = 0 := by
        have hz : (fun ω => U ω * P[V | 𝓕.rightCont t] ω) =ᵐ[P] (fun _ => (0 : ℝ)) := by
          filter_upwards [hCE] with ω hω ; simp [hω]
        rw [integral_congr_ae hz] ; simp
  have hCell (j i : ℕ) : Integrable (F j i) P ∧ (∫ ω in A, F j i ω ∂P) = 0 := by
    let t : ℝ≥0 := s j i
    have hY : Measurable[𝓕.rightCont t] (Y j i) := by have hXm := (X.adapted t).mono (𝓕.le_rightCont t) le_rfl ; have hDm := (dividendStrategy_rightLimit_adapted_rightCont D hD.1.1) t ; exact (measurable_const.add hXm).sub hDm
    have hMask : MeasurableSet[𝓕.rightCont t] {ω : Ω | t < ρ ω} := by
      have he : {ω : Ω | t < ρ ω} = {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ t}ᶜ := by ext ω ; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, WithTop.coe_le_coe, not_le]
      rw [he] ; exact (hρstop t).compl
    have hDeriv : Measurable (fun y : ℝ => if y ∈ Icc a (b j) then deriv w y else 1) := by
      have heq : (fun y : ℝ => if y ∈ Icc a (b j) then deriv w y else 1) = (fun y => if y ∈ Icc a (b j) then (if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0) else 1) := by
        funext y ; by_cases hy : y ∈ Icc a (b j)
        · obtain ⟨hy0, hyC⟩ := (hBand j) hy ; simp [hy, hy0, hyC]
        · simp [hy]
      rw [heq] ; exact Measurable.ite measurableSet_Icc hGrad measurable_const
    have hHessian : Measurable (fun y : ℝ => if y ∈ Icc a (b j) then iteratedDeriv 2 w y else 0) := by
      have heq : (fun y : ℝ => if y ∈ Icc a (b j) then iteratedDeriv 2 w y else 0) = (fun y => if y ∈ Icc a (b j) then (if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0) else 0) := by
        funext y ; by_cases hy : y ∈ Icc a (b j)
        · obtain ⟨hy0, hyC⟩ := (hBand j) hy ; simp [hy, hy0, hyC]
        · simp [hy]
      rw [heq] ; exact Measurable.ite measurableSet_Icc hHess measurable_const
    have hGm : Measurable[𝓕.rightCont t] (G j i) := by
      change Measurable[𝓕.rightCont t] (fun ω => if t < ρ ω then Real.exp (-(q * (t : ℝ))) * (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω) else 1) else 0)
      exact Measurable.ite hMask (measurable_const.mul (hDeriv.comp hY)) measurable_const
    have hHm : Measurable[𝓕.rightCont t] (H j i) := by
      change Measurable[𝓕.rightCont t] (fun ω => if t < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) * (if Y j i ω ∈ Icc a (b j) then iteratedDeriv 2 w (Y j i ω) else 0) else 0)
      exact Measurable.ite hMask
        ((measurable_const.mul measurable_const).mul (hHessian.comp hY)) measurable_const
    obtain ⟨KG, KH, hKG, hKH, hGB, hHB⟩ := avram_f16_original_ubv_zerojump_compact_C2_discount_envelope X hBV hν q (le_of_lt hq) C w hw_smooth hOpen a (b j) (hBand j)
    have hExp : Real.exp (-(q * (t : ℝ))) ≤ 1 := by apply Real.exp_le_one_iff.mpr ; have ht : 0 ≤ (t : ℝ) := t.property ; nlinarith [mul_nonneg (le_of_lt hq) ht]
    have hGb : ∀ ω, |G j i ω| ≤ max KG 1 := by
      intro ω ; by_cases hs : t < ρ ω
      · by_cases hy : Y j i ω ∈ Icc a (b j)
        · have hg := hGB t (Y j i ω) hy ; simpa only [G, t, if_pos hs, if_pos hy] using le_trans hg (le_max_left KG 1)
        · have hh : |Real.exp (-(q * (t : ℝ))) * (1 : ℝ)| ≤ 1 := by simpa [abs_of_pos (Real.exp_pos _)] using hExp
          simpa only [G, t, if_pos hs, if_neg hy] using le_trans hh (le_max_right KG 1)
      · simp only [G, t, if_neg hs, abs_zero] ; exact le_trans hKG (le_max_left KG 1)
    have hHb : ∀ ω, |H j i ω| ≤ KH := by
      intro ω ; by_cases hs : t < ρ ω
      · by_cases hy : Y j i ω ∈ Icc a (b j)
        · have hh := hHB t (Y j i ω) hy
          have hhalf : |(1 / 2 : ℝ) * (Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w (Y j i ω))| ≤ KH := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)] ; nlinarith
          simpa only [H, t, if_pos hs, if_pos hy] using (show |(1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w (Y j i ω)| ≤ KH by convert hhalf using 1 <;> ring)
        · simpa only [H, t, if_pos hs, if_neg hy, mul_zero, abs_zero] using hKH
      · simp [H, t, hs, hKH]
    have hZ := avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero X hν t (t + Δ j) (le_add_of_nonneg_right bot_le)
    have hQ := avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero X hν t (t + Δ j) (le_add_of_nonneg_right bot_le)
    have hZI : Integrable (Z j i) P ∧ (P[Z j i | 𝓕.rightCont t] =ᵐ[P] fun _ => (0 : ℝ)) := by simpa only [Z, t, NNReal.coe_add, add_sub_cancel_left] using hZ
    have hQI : Integrable (Q j i) P ∧ (P[Q j i | 𝓕.rightCont t] =ᵐ[P] fun _ => (0 : ℝ)) := by simpa only [Q, Z, t, NNReal.coe_add, add_sub_cancel_left] using hQ
    have hGI := hWeighted t (G j i) (Z j i) (max KG 1) hGm hGb hZI.1 hZI.2
    have hHI := hWeighted t (H j i) (Q j i) KH hHm hHb hQI.1 hQI.2
    have hFI : Integrable (F j i) P := hGI.1.add hHI.1
    have hAin : MeasurableSet[𝓕.rightCont t] A :=
      ((𝓕.rightCont).mono (show (0 : ℝ≥0) ≤ t from bot_le) A) hA
    have hAG : Measurable[𝓕.rightCont t] (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * G j i ω) := (measurable_const.indicator hAin).mul hGm
    have hAH : Measurable[𝓕.rightCont t] (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * H j i ω) := (measurable_const.indicator hAin).mul hHm
    have hAGb : ∀ ω, |A.indicator (fun _ => (1 : ℝ)) ω * G j i ω| ≤ max KG 1 := by
      intro ω ; by_cases haω : ω ∈ A
      · simpa [Set.indicator, haω] using hGb ω
      · simp [Set.indicator, haω, hKG]
    have hAHb : ∀ ω, |A.indicator (fun _ => (1 : ℝ)) ω * H j i ω| ≤ KH := by
      intro ω ; by_cases haω : ω ∈ A
      · simpa [Set.indicator, haω] using hHb ω
      · simp [Set.indicator, haω, hKH]
    have hAG0 := hWeighted t _ _ _ hAG hAGb hZI.1 hZI.2
    have hAH0 := hWeighted t _ _ _ hAH hAHb hQI.1 hQI.2
    have hAA : MeasurableSet A := (𝓕.rightCont.le 0 A) hA
    have hZ0 : (∫ ω in A, G j i ω * Z j i ω ∂P) = 0 := by
      have heq : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * G j i ω * Z j i ω) = A.indicator (fun ω => G j i ω * Z j i ω) := by
        funext ω ; by_cases hw : ω ∈ A <;> simp [Set.indicator, hw]
      rw [heq] at hAG0
      simpa only [integral_indicator hAA] using hAG0.2
    have hQ0 : (∫ ω in A, H j i ω * Q j i ω ∂P) = 0 := by
      have heq : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * H j i ω * Q j i ω) = A.indicator (fun ω => H j i ω * Q j i ω) := by
        funext ω ; by_cases hw : ω ∈ A <;> simp [Set.indicator, hw]
      rw [heq] at hAH0
      simpa only [integral_indicator hAA] using hAH0.2
    refine ⟨hFI, ?_⟩ ; change (∫ ω in A, G j i ω * Z j i ω + H j i ω * Q j i ω ∂P) = 0
    rw [integral_add (hGI.1.integrableOn) (hHI.1.integrableOn)] ; simp [hZ0, hQ0]
  constructor
  · intro j ; have hI : Integrable (M j) P := integrable_finset_sum _ (fun i hi => (hCell j i).1)
    exact hI.integrableOn
  · intro j ; change (∫ ω in A, ∑ i ∈ Finset.range (N j + 1), F j i ω ∂P) = 0 ; rw [integral_finset_sum _ (fun i hi => (hCell j i).1.integrableOn)] ; exact Finset.sum_eq_zero (fun i hi => (hCell j i).2)
