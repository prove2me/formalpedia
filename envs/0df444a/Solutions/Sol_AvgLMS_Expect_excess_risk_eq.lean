-- Prove2me | solution 1 for AvgLMS.Expect.excess_risk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:00:03.965127+00:00
-- url     : https://prove2.me/submissions/916fb4f4-985a-4d2f-80fc-1c503d401f00

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

open AvgLMS.Expect in
theorem AvgLMS_excess_aux_formula {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ) (θ : Hs d) :
    lsObjective μ x z θ = (1 / 2) * ⟪θ, H θ⟫_ℝ - ⟪θ, ∫ ω, z 1 ω ∂μ⟫_ℝ := by
  have hz : Integrable (z 1) μ := hA.memLp_z.integrable (by norm_num)
  have h1 : Integrable (fun ω => ⟪θ, x 1 ω⟫_ℝ ^ 2) μ := by
    refine (hA.integrable_cov θ θ).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [real_inner_comm θ (x 1 ω)]; ring
  have h2 : Integrable (fun ω => 2 * ⟪θ, z 1 ω⟫_ℝ) μ := (hz.inner_const θ |>.congr
    (Filter.Eventually.of_forall fun ω => by simp [real_inner_comm])).const_mul 2
  unfold lsObjective
  rw [integral_sub h1 h2, integral_const_mul, ← integral_inner hz, hA.cov_eq θ θ]
  have : ∫ ω, ⟪θ, x 1 ω⟫_ℝ ^ 2 ∂μ = ∫ ω, ⟪x 1 ω, θ⟫_ℝ * ⟪x 1 ω, θ⟫_ℝ ∂μ := by
    congr 1; funext ω; rw [real_inner_comm θ (x 1 ω)]; ring
  rw [this]; ring

open MeasureTheory ProbabilityTheory InnerProductSpace RealInnerProductSpace AvgLMS.Expect in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ) :
    ∀ θ : Hs d, lsObjective μ x z θ - lsObjective μ x z θstar =
      (1 / 2) * ⟪θ - θstar, H (θ - θstar)⟫_ℝ := by
  set b : Hs d := ∫ ω, z 1 ω ∂μ with hb
  have hf : ∀ θ, lsObjective μ x z θ = (1 / 2) * ⟪θ, H θ⟫_ℝ - ⟪θ, b⟫_ℝ :=
    AvgLMS_excess_aux_formula μ x z H θstar R σ hA
  have hsymm : ∀ v w : Hs d, ⟪v, H w⟫_ℝ = ⟪w, H v⟫_ℝ := by
    intro v w; rw [hA.cov_eq v w, hA.cov_eq w v]; congr 1; funext ω; ring
  have hpos : ∀ v : Hs d, 0 ≤ ⟪v, H v⟫_ℝ := by
    intro v; rw [hA.cov_eq v v]; exact integral_nonneg fun ω => mul_self_nonneg _
  -- first-order condition
  have hgrad : ∀ v : Hs d, ⟪v, H θstar⟫_ℝ = ⟪v, b⟫_ℝ := by
    intro v
    have key : ∀ t : ℝ, 0 ≤ t * (⟪v, H θstar⟫_ℝ - ⟪v, b⟫_ℝ) + t ^ 2 / 2 * ⟪v, H v⟫_ℝ := by
      intro t
      have h := hA.isMin (θstar + t • v)
      rw [hf, hf] at h
      simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, RCLike.conj_to_real] at h
      rw [hsymm θstar v] at h
      nlinarith
    set c := ⟪v, H θstar⟫_ℝ - ⟪v, b⟫_ℝ
    set a := ⟪v, H v⟫_ℝ
    have ha := hpos v
    have hk := key (-c / (a + 1))
    have hc : c ^ 2 ≤ 0 := by
      have ha1 : 0 < a + 1 := by linarith
      have e : -c / (a + 1) * c + (-c / (a + 1)) ^ 2 / 2 * a
          = c ^ 2 / (a + 1) * (a / (2 * (a + 1)) - 1) := by field_simp; ring
      rw [e] at hk
      have hneg : a / (2 * (a + 1)) - 1 < 0 := by
        rw [sub_neg, div_lt_one (by linarith)]; linarith
      have : 0 ≤ c ^ 2 / (a + 1) := div_nonneg (sq_nonneg c) ha1.le
      by_contra hcon
      have hcon' : 0 < c ^ 2 := lt_of_not_ge hcon
      have : 0 < c ^ 2 / (a + 1) := div_pos hcon' ha1
      nlinarith
    have : c = 0 := by nlinarith [sq_nonneg c]
    linarith
  intro θ
  rw [hf, hf]
  simp only [map_sub, inner_sub_left, inner_sub_right]
  rw [← hgrad θ, ← hgrad θstar, hsymm θstar θ]
  ring
