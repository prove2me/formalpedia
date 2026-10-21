-- Prove2me | solution 1 for DirectedSearch.Approx.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:05:53.254714+00:00
-- url     : https://prove2.me/submissions/72c4efd0-1dfd-47c7-ac5a-558623e29c89

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

set_option autoImplicit false
open MeasureTheory DirectedSearch.Approx Set

section dsacore
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

lemma dsa_tailMass_eq (τ : ℝ) : tailMass μ τ = ∫ x in Ici τ, (1:ℝ) ∂μ := by
  simp [tailMass, Measure.real]

lemma dsa_tailMass_nonneg (τ : ℝ) : 0 ≤ tailMass μ τ := ENNReal.toReal_nonneg

lemma dsa_cont_tailMass : Continuous (tailMass μ) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have h : ∀ a : ℝ, ContinuousOn (fun b => ∫ x in Ici b, (1:ℝ) ∂μ) (Ici a) := fun a =>
    (integrableOn_const (by simp)).continuousOn_Ici_primitive_Ici
  have h2 := (h (τ - 1)).continuousAt (Ici_mem_nhds (by linarith))
  have : tailMass μ = fun b => ∫ x in Ici b, (1:ℝ) ∂μ := funext (dsa_tailMass_eq μ)
  rw [this]; exact h2

lemma dsa_cont_tailInt (hint : Integrable id μ) : Continuous (tailInt μ) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have h : ∀ a : ℝ, ContinuousOn (fun b => ∫ x in Ici b, x ∂μ) (Ici a) := fun a =>
    (hint.integrableOn : IntegrableOn id (Ici a) μ).continuousOn_Ici_primitive_Ici
  exact (h (τ - 1)).continuousAt (Ici_mem_nhds (by linarith))

lemma dsa_split (hint : Integrable id μ) {a b : ℝ} (h : a ≤ b) :
    tailInt μ a = tailInt μ b + ∫ x in Ico a b, x ∂μ ∧
    tailMass μ a = tailMass μ b + (μ (Ico a b)).toReal ∧
    a * (μ (Ico a b)).toReal ≤ ∫ x in Ico a b, x ∂μ ∧
    ∫ x in Ico a b, x ∂μ ≤ b * (μ (Ico a b)).toReal := by
  have hU : Ici a = Ico a b ∪ Ici b := (Ico_union_Ici_eq_Ici h).symm
  have hD : Disjoint (Ico a b) (Ici b) := Set.disjoint_left.2 (fun x hx hy => absurd hx.2 (not_lt.2 hy))
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tailInt
    have e := setIntegral_union (μ := μ) (f := fun x : ℝ => x) hD measurableSet_Ici
      (hint.integrableOn) (hint.integrableOn)
    rw [hU]; linarith
  · unfold tailMass
    rw [hU, measure_union hD measurableSet_Ici, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      add_comm]
  · have := setIntegral_mono_on (μ := μ) (s := Ico a b) (f := fun _ => a) (g := fun x => x)
      (integrableOn_const (by simp)) (hint.integrableOn) measurableSet_Ico
      (fun x hx => hx.1)
    simpa [Measure.real, mul_comm] using this
  · have := setIntegral_mono_on (μ := μ) (s := Ico a b) (f := fun x => x) (g := fun _ => b)
      (hint.integrableOn) (integrableOn_const (by simp)) measurableSet_Ico
      (fun x hx => hx.2.le)
    simpa [Measure.real, mul_comm] using this

lemma dsa_A_a (hint : Integrable id μ) {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (hab : a < b)
    (hb : b ≤ ratio μ δ b) : ratio μ δ a ≤ ratio μ δ b := by
  obtain ⟨hI, hT, hJ1, hJ2⟩ := dsa_split μ hint hab.le
  have hK : 0 ≤ (μ (Ico a b)).toReal := ENNReal.toReal_nonneg
  have hT' := dsa_tailMass_nonneg μ b
  have hD : 0 < δ + tailMass μ b := by linarith
  unfold ratio at *
  rw [hI, hT]
  rw [le_div_iff₀ hD] at hb
  rw [div_le_div_iff₀ (by positivity) hD]
  set K := (μ (Ico a b)).toReal
  set J := ∫ x in Ico a b, x ∂μ
  set I' := tailInt μ b
  set T' := tailMass μ b
  nlinarith [mul_le_mul_of_nonneg_right hJ2 hD.le, mul_le_mul_of_nonneg_left hb hK]

lemma dsa_A_b (hint : Integrable id μ) {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (hab : a < b)
    (ha : ratio μ δ a ≤ a) : ratio μ δ b ≤ ratio μ δ a := by
  obtain ⟨hI, hT, hJ1, hJ2⟩ := dsa_split μ hint hab.le
  have hK : 0 ≤ (μ (Ico a b)).toReal := ENNReal.toReal_nonneg
  have hT' := dsa_tailMass_nonneg μ b
  have hD : 0 < δ + tailMass μ b := by linarith
  unfold ratio at *
  rw [hI, hT] at ha ⊢
  have hD2 : 0 < δ + (tailMass μ b + (μ (Ico a b)).toReal) := by linarith
  rw [div_le_iff₀ hD2] at ha
  rw [div_le_div_iff₀ hD hD2]
  set K := (μ (Ico a b)).toReal
  set J := ∫ x in Ico a b, x ∂μ
  set I' := tailInt μ b
  set T' := tailMass μ b
  have h1 : I' * K ≤ (a * (δ + (T' + K)) - J) * K := by
    apply mul_le_mul_of_nonneg_right _ hK; linarith
  have h2 : a * K * (δ + (T' + K)) ≤ J * (δ + (T' + K)) := mul_le_mul_of_nonneg_right hJ1 hD2.le
  nlinarith [h1, h2]

lemma dsa_ratio_le (hint : Integrable id μ) {δ : ℝ} (hδ : 0 < δ) (τ : ℝ) :
    ratio μ δ τ ≤ (∫ x, |x| ∂μ) / δ := by
  have hM : 0 ≤ ∫ x, |x| ∂μ := integral_nonneg fun x => abs_nonneg x
  have hI : tailInt μ τ ≤ ∫ x, |x| ∂μ := by
    unfold tailInt
    calc ∫ x in Ici τ, x ∂μ ≤ ∫ x in Ici τ, |x| ∂μ :=
          setIntegral_mono_on (hint.integrableOn) (hint.abs.integrableOn) measurableSet_Ici
            (fun x _ => le_abs_self x)
      _ ≤ ∫ x, |x| ∂μ := setIntegral_le_integral hint.abs (Filter.Eventually.of_forall fun x => abs_nonneg x)
  unfold ratio
  have hT := dsa_tailMass_nonneg μ τ
  have hD : 0 < δ + tailMass μ τ := by linarith
  rcases le_or_gt (tailInt μ τ) 0 with h | h
  · exact (div_nonpos_of_nonpos_of_nonneg h hD.le).trans (div_nonneg hM hδ.le)
  · calc tailInt μ τ / (δ + tailMass μ τ) ≤ tailInt μ τ / δ :=
          div_le_div_of_nonneg_left h.le hδ (by linarith)
      _ ≤ (∫ x, |x| ∂μ) / δ := div_le_div_of_nonneg_right hI hδ.le

lemma dsa_ratio_zero_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ ratio μ δ 0 := by
  unfold ratio
  have hT := dsa_tailMass_nonneg μ 0
  refine div_nonneg ?_ (by linarith)
  exact setIntegral_nonneg measurableSet_Ici (fun x hx => hx)

lemma dsa_ratio_cont (hint : Integrable id μ) {δ : ℝ} (hδ : 0 < δ) : Continuous (ratio μ δ) := by
  unfold ratio
  refine (dsa_cont_tailInt μ hint).div (continuous_const.add (dsa_cont_tailMass μ)) fun τ => ?_
  have := dsa_tailMass_nonneg μ τ
  linarith

/-- a fixed point of `ratio` in `[0, ∞)` exists -/
lemma dsa_fixed (hint : Integrable id μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ0 : ℝ, 0 ≤ τ0 ∧ ratio μ δ τ0 = τ0 := by
  set M0 := (∫ x, |x| ∂μ) / δ with hM0
  have hM : 0 ≤ M0 := div_nonneg (integral_nonneg fun x => abs_nonneg x) hδ.le
  have hc : Continuous (fun τ => ratio μ δ τ - τ) := (dsa_ratio_cont μ hint hδ).sub continuous_id
  have h0 : (0:ℝ) ∈ Icc ((fun τ => ratio μ δ τ - τ) M0) ((fun τ => ratio μ δ τ - τ) 0) := by
    constructor
    · simp only
      linarith [dsa_ratio_le μ hint hδ M0]
    · simp only
      linarith [dsa_ratio_zero_nonneg μ hδ]
  obtain ⟨τ0, hτ0, hτ⟩ := intermediate_value_Icc' hM hc.continuousOn h0
  exact ⟨τ0, hτ0.1, by simp only at hτ; linarith⟩
end dsacore

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hint : Integrable id μ) (δ : ℝ) (hδ : 0 < δ) :
    let ρ := sSup (ratio μ δ '' Set.Ici 0)
    (∃ τ, 0 ≤ τ ∧ ratio μ δ τ = ρ) ∧ ratio μ δ ρ = ρ ∧
      MonotoneOn (ratio μ δ) (Set.Iic ρ) ∧ AntitoneOn (ratio μ δ) (Set.Ici ρ) := by
  intro ρ
  obtain ⟨τ0, hτ0, hfix⟩ := dsa_fixed μ hint hδ
  have hU : ∀ τ, ratio μ δ τ ≤ τ0 := by
    intro τ
    rcases lt_trichotomy τ τ0 with h | h | h
    · have := dsa_A_a μ hint hδ h (by rw [hfix])
      rw [hfix] at this; exact this
    · rw [h, hfix]
    · have := dsa_A_b μ hint hδ h (by rw [hfix])
      rw [hfix] at this; exact this
  have hρ : ρ = τ0 := by
    apply IsGreatest.csSup_eq
    exact ⟨⟨τ0, hτ0, hfix⟩, by rintro _ ⟨τ, _, rfl⟩; exact hU τ⟩
  rw [hρ]
  have hlow : ∀ τ', τ' ≤ τ0 → τ' ≤ ratio μ δ τ' := by
    intro τ' h
    by_contra hcon
    have hlt := not_le.1 hcon
    have hne : τ' < τ0 := by
      rcases h.lt_or_eq with h1 | h1
      · exact h1
      · rw [h1, hfix] at hlt; exact absurd hlt (lt_irrefl _)
    have := dsa_A_b μ hint hδ hne hlt.le
    rw [hfix] at this
    linarith
  refine ⟨⟨τ0, hτ0, hfix⟩, hfix, ?_, ?_⟩
  · intro a ha b hb hab
    rcases hab.lt_or_eq with h | h
    · exact dsa_A_a μ hint hδ h (hlow b hb)
    · rw [h]
  · intro a ha b hb hab
    rcases hab.lt_or_eq with h | h
    · exact dsa_A_b μ hint hδ h ((hU a).trans ha)
    · rw [h]
