-- Prove2me | solution 1 for FiniteEnergyPlane.exists_injective_of_weighted_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T16:38:04.505813+00:00
-- url     : https://prove2.me/submissions/76124fb9-ea35-4228-90fc-0f5fe2af530b

import Mathlib



namespace FiniteEnergyPlane

open Metric Filter Topology

/-- Let `B : ℂ → E` satisfy `c ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) ‖B z - B z'‖` for all `z, z'`. Then there
is `ε > 0` such that every differentiable `A` with `‖A z - B z‖ ≤ ε` and
`(1 + ‖z‖) ‖DA(z) - DB(z)‖ ≤ ε` for all `z` is injective with injective derivative everywhere. -/
theorem exists_injective_of_weighted_lower_bound_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (hc : 0 < c) :
    ∃ ε > 0, ∀ A B : ℂ → E, Differentiable ℝ A → Differentiable ℝ B →
      (∀ z z', c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) * ‖B z - B z'‖) →
      (∀ z, ‖A z - B z‖ ≤ ε) →
      (∀ z, (1 + ‖z‖) * ‖fderiv ℝ A z - fderiv ℝ B z‖ ≤ ε) →
      Function.Injective A ∧ ∀ z, Function.Injective (fderiv ℝ A z) := by
  refine ⟨c / 16, by positivity, fun A B hA hB hlow h0 h1 => ?_⟩
  set ε : ℝ := c / 16 with hε
  have hεpos : 0 < ε := by positivity
  set D : ℂ → E := fun z => A z - B z with hD
  have hDd : ∀ z, HasFDerivAt D (fderiv ℝ A z - fderiv ℝ B z) z := fun z =>
    (hA z).hasFDerivAt.sub (hB z).hasFDerivAt
  -- difference bound for `D`
  have hDdiff : ∀ z z' : ℂ, (1 + ‖z‖ + ‖z'‖) * ‖D z - D z'‖ ≤ 8 * ε * ‖z - z'‖ := by
    intro z z'
    set S : ℝ := 1 + ‖z‖ + ‖z'‖ with hS
    have hSpos : 0 < S := by positivity
    by_cases hfar : S / 4 ≤ ‖z - z'‖
    · have h2 : ‖D z - D z'‖ ≤ 2 * ε := by
        have := norm_sub_le (D z) (D z')
        have h3 := h0 z
        have h4 := h0 z'
        simp only [hD] at this ⊢
        linarith
      nlinarith [norm_nonneg (D z - D z')]
    · push_neg at hfar
      have hder : ∀ w ∈ segment ℝ z' z, ‖fderiv ℝ A w - fderiv ℝ B w‖ ≤ 4 * ε / S := by
        intro w hw
        obtain ⟨α, β, hα, hβ, hαβ, hw'⟩ := hw
        have hβe : β = 1 - α := by linarith
        have hα1 : α ≤ 1 := by linarith
        have hβ1 : β ≤ 1 := by linarith
        have hw1 : ‖z - w‖ ≤ ‖z - z'‖ := by
          have e : z - w = α • (z - z') := by
            rw [← hw', hβe]; module
          rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
          nlinarith [norm_nonneg (z - z')]
        have hw2 : ‖z' - w‖ ≤ ‖z - z'‖ := by
          have e : z' - w = (-β) • (z - z') := by
            rw [← hw', hβe]; module
          rw [e, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hβ]
          nlinarith [norm_nonneg (z - z')]
        have ht1 : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
          have := norm_add_le w (z - w)
          simpa using this
        have ht2 : ‖z'‖ ≤ ‖w‖ + ‖z' - w‖ := by
          have := norm_add_le w (z' - w)
          simpa using this
        have hwS : S / 4 ≤ 1 + ‖w‖ := by
          rw [hS] at hfar ⊢
          linarith
        have := h1 w
        rw [le_div_iff₀ hSpos]
        have hn := norm_nonneg (fderiv ℝ A w - fderiv ℝ B w)
        nlinarith
      have hmvt := (convex_segment z' z).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := D) (fun w _ => (hDd w).hasFDerivWithinAt) hder
        (right_mem_segment ℝ z' z) (left_mem_segment ℝ z' z)
      rw [norm_sub_rev z' z] at hmvt
      have hmvt' : ‖D z' - D z‖ ≤ 4 * ε / S * ‖z - z'‖ := by
        simpa using hmvt
      rw [norm_sub_rev] at hmvt'
      calc S * ‖D z - D z'‖ ≤ S * (4 * ε / S * ‖z - z'‖) := by gcongr
        _ = 4 * ε * ‖z - z'‖ := by field_simp
        _ ≤ 8 * ε * ‖z - z'‖ := by
            have := norm_nonneg (z - z')
            nlinarith
  -- lower bound for `A`
  have hAlow : ∀ z z' : ℂ, c / 2 * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) * ‖A z - A z'‖ := by
    intro z z'
    have hSpos : 0 < 1 + ‖z‖ + ‖z'‖ := by positivity
    have h2 : ‖B z - B z'‖ ≤ ‖A z - A z'‖ + ‖D z - D z'‖ := by
      have : B z - B z' = (A z - A z') - (D z - D z') := by simp only [hD]; abel
      rw [this]
      exact norm_sub_le _ _
    have h3 := hlow z z'
    have h4 := hDdiff z z'
    have h5 : (1 + ‖z‖ + ‖z'‖) * ‖B z - B z'‖ ≤
        (1 + ‖z‖ + ‖z'‖) * ‖A z - A z'‖ + (1 + ‖z‖ + ‖z'‖) * ‖D z - D z'‖ := by
      rw [← mul_add]; gcongr
    have h6 : 8 * ε = c / 2 := by rw [hε]; ring
    rw [h6] at h4
    linarith
  refine ⟨fun z z' h => ?_, fun z => ?_⟩
  · have := hAlow z z'
    rw [h, sub_self, norm_zero, mul_zero] at this
    have hn : ‖z - z'‖ ≤ 0 := by
      by_contra hh
      push_neg at hh
      have : 0 < c / 2 * ‖z - z'‖ := by positivity
      linarith
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hn)
  · rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set δ : ℝ := c / 2 * ‖v‖ / (2 * (2 + 2 * ‖z‖ + ‖v‖)) with hδ
    have hδpos : 0 < δ := by positivity
    have hl : HasFDerivAt A (fderiv ℝ A z) z := (hA z).hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => A (z + t • v)) (fderiv ℝ A z v) 0 :=
      hl.hasLineDerivAt v
    rw [hv] at hline
    have hlo := hline.isLittleO.def hδpos
    have hball : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioc (0 : ℝ) 1 :=
      Ioc_mem_nhdsGT (by norm_num)
    obtain ⟨t, ht1, ⟨ht0, ht1'⟩⟩ :=
      ((hlo.filter_mono nhdsWithin_le_nhds).and hball).exists
    simp only [sub_zero, zero_smul, add_zero, smul_zero, Real.norm_eq_abs, abs_of_pos ht0] at ht1
    have h2 := hAlow (z + t • v) z
    have hn1 : ‖z + t • v - z‖ = t * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    rw [hn1] at h2
    have hS : 1 + ‖z + t • v‖ + ‖z‖ ≤ 2 + 2 * ‖z‖ + ‖v‖ := by
      have h3 : ‖z + t • v‖ ≤ ‖z‖ + t * ‖v‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have h4 : t * ‖v‖ ≤ ‖v‖ := by nlinarith
      linarith
    have hP : 0 < 2 + 2 * ‖z‖ + ‖v‖ := by positivity
    have h5 : (1 + ‖z + t • v‖ + ‖z‖) * ‖A (z + t • v) - A z‖ ≤
        (2 + 2 * ‖z‖ + ‖v‖) * (δ * t) := by
      gcongr
    have h6 : (2 + 2 * ‖z‖ + ‖v‖) * (δ * t) = c / 2 * ‖v‖ / 2 * t := by
      rw [hδ]; field_simp
    have h7 : c / 2 * (t * ‖v‖) ≤ c / 2 * ‖v‖ / 2 * t := by
      calc _ ≤ _ := h2
        _ ≤ _ := h5
        _ = _ := h6
    have h8 : 0 < c * ‖v‖ * t := by positivity
    nlinarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (hc : 0 < c) :
    ∃ ε > 0, ∀ A B : ℂ → E, Differentiable ℝ A → Differentiable ℝ B →
      (∀ z z', c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) * ‖B z - B z'‖) →
      (∀ z, ‖A z - B z‖ ≤ ε) →
      (∀ z, (1 + ‖z‖) * ‖fderiv ℝ A z - fderiv ℝ B z‖ ≤ ε) →
      Function.Injective A ∧ ∀ z, Function.Injective (fderiv ℝ A z) :=
  exists_injective_of_weighted_lower_bound_aux c hc
