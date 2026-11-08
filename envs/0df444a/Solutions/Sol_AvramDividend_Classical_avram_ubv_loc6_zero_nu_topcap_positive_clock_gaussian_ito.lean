-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_zero_nu_topcap_positive_clock_gaussian_ito
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:24:54.126741+00:00
-- url     : https://prove2.me/submissions/21840c19-b2a0-4c62-aa25-7d429d5d9c93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_gaussian_masked_expected_topcap
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian11_conditional_budget_zero_clock_centering
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, ∃ Mc G R : Ω → ℝ,
      Integrable Mc P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∀ ω, σ k ω = 0 → Mc ω = 0) ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, σ k ω ≠ 0 →
        F k ω ≤ w x + Mc ω + G ω + R ω) := by
  classical
  haveI := X.isProbability
  intro k
  have hSigmaNonzero : X.σ ≠ 0 := by intro h0; exact hBV ⟨h0, by rw [hν]; simp⟩
  have hMask : (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P) ≤ w x :=
    AvramDividend.Classical.avram_ubv_loc6_gaussian_masked_expected_topcap X hX hBV hSigmaNonzero hν q hq w C hC hTopCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm hTermMeas hCashI σ F hσstop hσle hFsource hFI k
  have hσmeas : Measurable (fun ω => ((σ k ω : ℝ≥0) : WithTop ℝ≥0)) := (hσstop k).measurable.mono (hσstop k).measurableSpace_le le_rfl
  have hZero : MeasurableSet {ω : Ω | σ k ω = 0} := by
    have hPre : MeasurableSet (((fun ω => ((σ k ω : ℝ≥0) : WithTop ℝ≥0)) ⁻¹' {(0 : WithTop ℝ≥0)})) := hσmeas (measurableSet_singleton (0 : WithTop ℝ≥0))
    have heq : {ω : Ω | σ k ω = 0} = ((fun ω => ((σ k ω : ℝ≥0) : WithTop ℝ≥0)) ⁻¹' {(0 : WithTop ℝ≥0)}) := by ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]; exact WithTop.coe_inj.symm
    rwa [heq]
  let A0 : Set Ω := {ω | σ k ω = 0}
  have hA0 : MeasurableSet A0 := hZero
  let A : Set Ω := A0ᶜ
  have hA : MeasurableSet A := hA0.compl
  have hAeq : A = A0ᶜ := rfl
  have hMaskInt : Integrable (fun ω => if σ k ω = 0 then w x else F k ω) P := AvramDividend.Classical.avram_ubv_loc6_rightcont_stopping_zero_mask_integrable (σ k) (hσstop k) (F k) (hFI k) (w x)
  have hEqA : (∫ ω in A, (if σ k ω = 0 then w x else F k ω) ∂P) = (∫ ω in A, F k ω ∂P) := by apply MeasureTheory.setIntegral_congr_fun hA; intro ω hmem; simp only [A, A0, Set.mem_compl_iff, Set.mem_setOf_eq] at hmem; simp [hmem]
  have hEq0 : (∫ ω in A0, (if σ k ω = 0 then w x else F k ω) ∂P) = (∫ ω in A0, (w x : ℝ) ∂P) := by apply MeasureTheory.setIntegral_congr_fun hA0; intro ω hmem; simp only [A0, Set.mem_setOf_eq] at hmem; simp [hmem]
  have hAdd : (∫ ω in A0, (if σ k ω = 0 then w x else F k ω) ∂P) + (∫ ω in A, (if σ k ω = 0 then w x else F k ω) ∂P) = (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P) := by have h := MeasureTheory.integral_add_compl hA0 hMaskInt; rw [← hAeq] at h; exact h
  have hReal : MeasureTheory.Measure.real P A0 = (P A0).toReal := by
    simp [MeasureTheory.Measure.real]
  have hConst : (∫ _ in A0, (w x : ℝ) ∂P) = w x * (P A0).toReal := by
    simp only [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm, hReal]
  have hSplitF : (∫ ω, F k ω ∂P) = (∫ ω in A, F k ω ∂P) + (∫ ω in A0, F k ω ∂P) := by
    have h := MeasureTheory.integral_add_compl hA (hFI k)
    have hAcompl : Aᶜ = A0 := by
      rw [hAeq, compl_compl]
    rw [hAcompl] at h
    exact h.symm
  have hBudget : (∫ ω in A, F k ω ∂P) ≤ w x * (P A).toReal := by
    have hU : P A0 + P A = P univ := by
      have h := MeasureTheory.measure_add_measure_compl (μ := P) hA0
      rwa [← hAeq] at h
    have hP : (P A0).toReal + (P A).toReal = 1 := by
      have h1 : P univ = 1 := MeasureTheory.measure_univ
      have e1 : P A0 ≠ ⊤ := MeasureTheory.measure_ne_top P A0
      have e2 : P A ≠ ⊤ := MeasureTheory.measure_ne_top P A
      calc (P A0).toReal + (P A).toReal
          = (P A0 + P A).toReal := by rw [ENNReal.toReal_add e1 e2]
        _ = (P univ).toReal := by rw [hU]
        _ = 1 := by rw [h1, ENNReal.toReal_one]
    have hP' : (P A).toReal + (P A0).toReal = 1 := by linarith [hP]
    have heq : (w x : ℝ) = w x * (P A).toReal + w x * (P A0).toReal := by
      calc (w x : ℝ) = w x * 1 := by rw [mul_one]
        _ = w x * ((P A).toReal + (P A0).toReal) := by rw [← hP']
        _ = w x * (P A).toReal + w x * (P A0).toReal := by rw [mul_add]
    linarith [hMask, hConst, hEq0, hEqA, hAdd, heq]
  by_cases hApos : 0 < (P A).toReal
  · obtain ⟨M, hMint, hM0, hMout, hMle⟩ := AvramDividend.Classical.avram_ubv_gaussian11_conditional_budget_zero_clock_centering A hA hApos (F k) (hFI k) (w x) hBudget
    refine ⟨M, fun _ => 0, fun _ => 0, hMint, hM0, ?_, ?_, ?_, ?_⟩
    · intro ω hω
      have hmem : ω ∉ A := by
        simp only [A, A0, Set.mem_compl_iff, Set.mem_setOf_eq, ne_eq] at hω ⊢
        exact not_not_intro hω
      exact hMout ω hmem
    · exact Filter.Eventually.of_forall (fun _ => le_refl _)
    · exact Filter.Eventually.of_forall (fun _ => le_refl _)
    · filter_upwards with ω
      intro hNe
      have hmem : ω ∈ A := by
        simp only [A, A0, Set.mem_compl_iff, Set.mem_setOf_eq, ne_eq] at hNe ⊢
        exact hNe
      have hle := hMle ω hmem
      simpa using hle
  · push_neg at hApos
    have hT0 : (P A).toReal = 0 := by
      have hnn : 0 ≤ (P A).toReal := ENNReal.toReal_nonneg
      linarith
    have hP0 : P A = 0 := by
      by_contra hne
      have eT : P A ≠ ⊤ := MeasureTheory.measure_ne_top P A
      have hp : 0 < (P A).toReal := ENNReal.toReal_pos hne eT
      linarith
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, integrable_const _, by simp, fun ω _ => rfl, Filter.Eventually.of_forall (fun _ => le_refl _), Filter.Eventually.of_forall (fun _ => le_refl _), ?_⟩
    have hAe : ∀ᵐ ω ∂P, ω ∉ A := by
      rw [ae_iff]
      simpa using hP0
    filter_upwards [hAe] with ω hω hNe
    exact absurd hNe hω
