-- Prove2me | solution 1 for DriverSurge.IC.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T09:14:50.885574+00:00
-- url     : https://prove2.me/submissions/aedd54d7-c0b0-449a-8626-ae71c15f4cd8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DriverSurge_IC_Process
import Definitions.Def_DriverSurge_IC_Pricing
import Theorems.Thm_DriverSurge_IC_lemma_1

open MeasureTheory Set


namespace SurgeT3Alg

lemma ic_alg (s0 s1 X0 Y0 X1 Y1 T0 T1 Q0 Q1 R1 R2 : ℝ) (hs0 : 0 < s0) (hs1 : 0 < s1)
    (hX0 : 0 < X0) (hY0 : 0 < Y0) (hY0le : Y0 ≤ s0 * X0) (hX1 : 0 < X1) (hY1 : 0 < Y1)
    (hY1le : Y1 ≤ s1 * X1) (hT0 : T0 = 1 + X0) (hT1 : T1 = 1 + X1) (hQ0 : Q0 = s0 + Y0)
    (hQ1 : Q1 = s1 + Y1) (hR : R1 < R2)
    (H : (s0 * T0 - Q0) * T1 * R2 < R1 * T0 * (T1 * s0 + Q1)) :
    ∃ g δ m0 m1 : ℝ, 0 < g ∧ 0 ≤ δ ∧ g < m0 ∧ g < m1 ∧
      (m0 * X0 + (-δ) * Y0) / T0 = R1 ∧ (m1 * X1 + δ * Y1) / T1 = R2 ∧
      X0 * (m0 - g) - g + δ * s0 = 0 ∧ X1 * (m1 - g) - g - δ * s1 = 0 := by
  have hT0p : 0 < T0 := by linarith
  have hT1p : 0 < T1 := by linarith
  have hQ0p : 0 < Q0 := by linarith
  have hQ1p : 0 < Q1 := by linarith
  have hA0 : 0 ≤ s0 * T0 - Q0 := by rw [hT0, hQ0]; nlinarith
  have hBp : 0 < T1 * s0 + Q1 := by positivity
  have hkey : T0 * (T1 * s0 + Q1) - T1 * (s0 * T0 - Q0) = T0 * Q1 + T1 * Q0 := by ring
  have hden : 0 < Q1 * T0 + Q0 * T1 := by positivity
  have hTB : 0 < T0 * (T1 * s0 + Q1) := by positivity
  have hR1 : 0 < R1 := by
    by_contra hneg
    push_neg at hneg
    rcases le_or_gt 0 R2 with h2 | h2
    · have h3 : 0 ≤ (s0 * T0 - Q0) * T1 * R2 := by positivity
      have h4 : R1 * T0 * (T1 * s0 + Q1) ≤ 0 := by
        have := mul_nonpos_of_nonpos_of_nonneg hneg hTB.le
        linarith [this]
      linarith
    · -- T1*A ≤ T0*B, R2 < 0
      have h3 : T1 * (s0 * T0 - Q0) ≤ T0 * (T1 * s0 + Q1) := by nlinarith
      have h4 : (s0 * T0 - Q0) * T1 * R2 ≥ T0 * (T1 * s0 + Q1) * R2 := by
        have := mul_le_mul_of_nonpos_right h3 h2.le
        linarith
      have h5 : T0 * (T1 * s0 + Q1) * R2 > T0 * (T1 * s0 + Q1) * R1 :=
        mul_lt_mul_of_pos_left hR hTB
      nlinarith
  have hR2 : 0 < R2 := by linarith
  obtain ⟨g, hgden⟩ : ∃ g, g * (Q1 * T0 + Q0 * T1) = Q1 * T0 * R1 + Q0 * T1 * R2 :=
    ⟨(Q1 * T0 * R1 + Q0 * T1 * R2) / (Q1 * T0 + Q0 * T1), by field_simp⟩
  have hQT0 : 0 < Q0 * T1 := by positivity
  have hQT1 : 0 < Q1 * T0 := by positivity
  have hgR1 : R1 < g := by
    have : R1 * (Q1 * T0 + Q0 * T1) < g * (Q1 * T0 + Q0 * T1) := by
      rw [hgden]; nlinarith
    exact lt_of_mul_lt_mul_right this hden.le
  have hgR2 : g < R2 := by
    have : g * (Q1 * T0 + Q0 * T1) < R2 * (Q1 * T0 + Q0 * T1) := by
      rw [hgden]; nlinarith
    exact lt_of_mul_lt_mul_right this hden.le
  obtain ⟨δ, hδQ1⟩ : ∃ δ, δ * Q1 = T1 * (R2 - g) := ⟨T1 * (R2 - g) / Q1, by field_simp⟩
  have hδQ0 : δ * Q0 = T0 * (g - R1) := by
    have : Q1 * (δ * Q0) = Q1 * (T0 * (g - R1)) := by
      have e : Q1 * (δ * Q0) = Q0 * (δ * Q1) := by ring
      rw [e, hδQ1]; linear_combination (-1 : ℝ) * hgden
    exact mul_left_cancel₀ (ne_of_gt hQ1p) this
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ δ * Q1 := by rw [hδQ1]; nlinarith
    exact nonneg_of_mul_nonneg_left this hQ1p
  -- m0 > g
  have hm0 : 0 < T0 * R1 + δ * Y0 - g * X0 := by
    have e1 : (T0 * R1 + δ * Y0 - g * X0) * Q0 = T0 * R1 * s0 - g * (s0 * T0 - Q0) := by
      have : δ * Y0 * Q0 = T0 * (g - R1) * Y0 := by rw [← hδQ0]; ring
      rw [hT0, hQ0] at this ⊢
      linear_combination this
    have e2 : (T0 * R1 * s0 - g * (s0 * T0 - Q0)) * (Q1 * T0 + Q0 * T1) =
        Q0 * (R1 * T0 * (T1 * s0 + Q1) - (s0 * T0 - Q0) * T1 * R2) := by
      linear_combination (-(s0 * T0 - Q0)) * hgden
    have h5 : 0 < Q0 * (R1 * T0 * (T1 * s0 + Q1) - (s0 * T0 - Q0) * T1 * R2) := by
      apply mul_pos hQ0p; linarith
    rw [← e2] at h5
    have h6 := pos_of_mul_pos_left h5 hden.le
    rw [← e1] at h6
    exact pos_of_mul_pos_left h6 hQ0p.le
  have hm1 : 0 < T1 * R2 - δ * Y1 - g * X1 := by
    have e1 : (T1 * R2 - δ * Y1 - g * X1) * Q1 = T1 * R2 * s1 + g * (Y1 - s1 * X1) := by
      have : δ * Y1 * Q1 = T1 * (R2 - g) * Y1 := by rw [← hδQ1]; ring
      rw [hT1, hQ1] at this ⊢
      linear_combination -this
    have h6 : 0 < T1 * R2 * s1 + g * (Y1 - s1 * X1) := by
      have a1 : g * (s1 * X1) ≤ R2 * (s1 * X1) := by
        apply mul_le_mul_of_nonneg_right hgR2.le; positivity
      have a2 : R2 * (s1 * X1) < R2 * (s1 * T1) := by
        apply mul_lt_mul_of_pos_left _ hR2
        rw [hT1]; nlinarith
      have a3 : 0 ≤ g * Y1 := mul_nonneg (by linarith) hY1.le
      nlinarith
    rw [← e1] at h6
    exact pos_of_mul_pos_left h6 hQ1p.le
  refine ⟨g, δ, (T0 * R1 + δ * Y0) / X0, (T1 * R2 - δ * Y1) / X1, by linarith, hδ0, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hX0]; linarith
  · rw [lt_div_iff₀ hX1]; linarith
  · rw [div_eq_iff (ne_of_gt hT0p)]
    field_simp
    ring
  · rw [div_eq_iff (ne_of_gt hT1p)]
    field_simp
    ring
  · have h := mul_div_cancel₀ (T0 * R1 + δ * Y0) (ne_of_gt hX0)
    linear_combination h + hδQ0 - δ * hQ0 + g * hT0
  · have h := mul_div_cancel₀ (T1 * R2 - δ * Y1) (ne_of_gt hX1)
    linear_combination h - hδQ1 + δ * hQ1 + g * hT1

lemma nonic_alg (s0 s1 X0 Y0 X1 Y1 T0 T1 Q0 Q1 R1 R2 : ℝ) (hs0 : 0 < s0) (hs1 : 0 < s1)
    (hX0 : 0 < X0) (hY0 : 0 < Y0) (hY0le : Y0 ≤ s0 * X0) (hX1 : 0 < X1) (hY1 : 0 < Y1)
    (hT0 : T0 = 1 + X0) (hT1 : T1 = 1 + X1) (hQ0 : Q0 = s0 + Y0)
    (hQ1 : Q1 = s1 + Y1) (hR2 : 0 ≤ R2)
    (H : R1 * T0 * (T1 * s0 + Q1) ≤ (s0 * T0 - Q0) * T1 * R2) :
    ∃ g u z0 m1 : ℝ, u * s0 = g ∧ 0 ≤ g ∧ 0 ≤ u ∧ g ≤ m1 ∧ z0 + u ≤ 0 ∧
      (g * X0 + z0 * Y0) / T0 = R1 ∧ (m1 * X1 + u * Y1) / T1 = R2 ∧
      X1 * (m1 - g) - g - u * s1 = 0 := by
  have hT0p : 0 < T0 := by linarith
  have hT1p : 0 < T1 := by linarith
  have hBp : 0 < T1 * s0 + Q1 := by rw [hQ1]; positivity
  obtain ⟨u, hu⟩ : ∃ u, u * (T1 * s0 + Q1) = T1 * R2 :=
    ⟨T1 * R2 / (T1 * s0 + Q1), by field_simp⟩
  have hu0 : 0 ≤ u := by
    have : 0 ≤ u * (T1 * s0 + Q1) := by rw [hu]; positivity
    exact nonneg_of_mul_nonneg_left this hBp
  set g := u * s0 with hg
  have hg0 : 0 ≤ g := by positivity
  -- s0 R1 T0 ≤ g A
  have hA : s0 * R1 * T0 ≤ g * (s0 * T0 - Q0) := by
    have h1 : (s0 * R1 * T0) * (T1 * s0 + Q1) ≤ (g * (s0 * T0 - Q0)) * (T1 * s0 + Q1) := by
      have e : (g * (s0 * T0 - Q0)) * (T1 * s0 + Q1) = s0 * ((s0 * T0 - Q0) * T1 * R2) := by
        rw [hg]; linear_combination (s0 * (s0 * T0 - Q0)) * hu
      rw [e]
      have := mul_le_mul_of_nonneg_left H hs0.le
      linarith
    exact le_of_mul_le_mul_right h1 hBp
  have hfin : X1 * ((T1 * R2 - u * Y1) / X1 - g) - g - u * s1 = 0 := by
    have h := mul_div_cancel₀ (T1 * R2 - u * Y1) (ne_of_gt hX1)
    rw [hg]
    linear_combination h - hu + u * s0 * hT1 + u * hQ1
  refine ⟨g, u, (R1 * T0 - g * X0) / Y0, (T1 * R2 - u * Y1) / X1, rfl, hg0, hu0, ?_, ?_, ?_,
    ?_, hfin⟩
  · have : 0 ≤ X1 * ((T1 * R2 - u * Y1) / X1 - g) := by
      have : 0 ≤ g + u * s1 := by positivity
      linarith
    have := nonneg_of_mul_nonneg_right (by linarith : 0 ≤ X1 * ((T1 * R2 - u * Y1) / X1 - g)) hX1
    linarith
  · rw [div_add' _ _ _ (ne_of_gt hY0), div_nonpos_iff]
    right
    refine ⟨?_, hY0.le⟩
    -- R1 T0 - g X0 + u Y0 ≤ 0  ⟸ s0 * (...) ≤ 0
    have h2 : s0 * (R1 * T0 - g * X0 + u * Y0) ≤ 0 := by
      have e : s0 * (R1 * T0 - g * X0 + u * Y0) = s0 * R1 * T0 - g * (s0 * T0 - Q0) := by
        rw [hg]; rw [hT0, hQ0]; ring
      rw [e]; linarith
    exact nonpos_of_mul_nonpos_right (by linarith) hs0
  · rw [div_eq_iff (ne_of_gt hT0p)]
    have h := mul_div_cancel₀ (R1 * T0 - g * X0) (ne_of_gt hY0)
    linear_combination h
  · rw [div_eq_iff (ne_of_gt hT1p)]
    have h := mul_div_cancel₀ (T1 * R2 - u * Y1) (ne_of_gt hX1)
    linear_combination h



lemma C_alg (s0 X0 Y0 T0 T1 Q0 Q1 : ℝ) (hs0 : 0 < s0) (hX0 : 0 < X0) (hY0 : 0 < Y0) (hY0le : Y0 ≤ s0 * X0)
    (hT0 : T0 = 1 + X0) (hT1p : 0 < T1) (hQ0 : Q0 = s0 + Y0) (hQ1p : 0 < Q1) :
    0 ≤ 1 - (1 / T0) * (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) ∧
    1 - (1 / T0) * (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) < 1 := by
  have hT0p : 0 < T0 := by linarith
  have hA : 0 ≤ s0 * T0 - Q0 := by rw [hT0, hQ0]; nlinarith
  have hB : 0 < T1 * s0 + Q1 := by positivity
  have hQ0p : 0 < Q0 := by rw [hQ0]; nlinarith
  have hD : 0 < Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1) := by positivity
  have hN : 0 < Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1) := by positivity
  have hNle : Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1) ≤
      T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) := by
    have e : T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) -
        (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) =
        Q1 * (s0 * T0 - Q0) * X0 + (T1 * s0 + Q1) * (s0 * T0 - Q0) := by
      rw [hT0]; ring
    have : 0 ≤ Q1 * (s0 * T0 - Q0) * X0 + (T1 * s0 + Q1) * (s0 * T0 - Q0) := by positivity
    linarith
  have e : (1 / T0) * (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) =
      (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1))) := by
    field_simp
  rw [e]
  have hTD : 0 < T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) := by positivity
  constructor
  · have : (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1))) ≤ 1 := by
      rw [div_le_one hTD]; exact hNle
    linarith
  · have : 0 < (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1))) := div_pos hN hTD
    linarith

lemma C_H (s0 X0 Y0 T0 T1 Q0 Q1 R1 R2 : ℝ) (hs0 : 0 < s0) (hX0 : 0 < X0) (hY0 : 0 < Y0) (hY0le : Y0 ≤ s0 * X0)
    (hT0 : T0 = 1 + X0) (hT1p : 0 < T1) (hQ0 : Q0 = s0 + Y0) (hQ1p : 0 < Q1) (hR2 : 0 < R2)
    (hC : 1 - (1 / T0) * (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) < R1 / R2) :
    (s0 * T0 - Q0) * T1 * R2 < R1 * T0 * (T1 * s0 + Q1) := by
  have hT0p : 0 < T0 := by linarith
  have hA : 0 ≤ s0 * T0 - Q0 := by rw [hT0, hQ0]; nlinarith
  have hB : 0 < T1 * s0 + Q1 := by positivity
  have hQ0p : 0 < Q0 := by rw [hQ0]; nlinarith
  have hD : 0 < Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1) := by positivity
  set C := 1 - (1 / T0) * (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) with hCdef
  have hCe : C * (T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1))) =
      T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) -
        (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) := by
    have hTne := hT0p.ne'
    have hDne := hD.ne'
    have h : (1 / T0) * (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
        (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) *
        (T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1))) =
        Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1) := by
      calc (1 / T0) * (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) /
            (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) *
            (T0 * (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)))
          = (Q1 * (s0 * T0 - Q0) + Q0 * (T1 * s0 + Q1)) * (T0 * T0⁻¹) *
            ((Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) *
              (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1))⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hTne, mul_inv_cancel₀ hDne]; ring
    rw [hCdef]; linear_combination (-1 : ℝ) * h
  have hCR : C * R2 < R1 := by rwa [lt_div_iff₀ hR2] at hC
  -- (C T0 B - A T1) D = A Q1 (B T0 - T1 A) ≥ 0
  have hid : (C * T0 * (T1 * s0 + Q1) - (s0 * T0 - Q0) * T1) *
      (Q1 * (s0 * T0 - Q0) + s0 * (T1 * s0 + Q1)) =
      (s0 * T0 - Q0) * Q1 * ((T1 * s0 + Q1) * T0 - T1 * (s0 * T0 - Q0)) := by
    linear_combination (T1 * s0 + Q1) * hCe
  have hpos : 0 ≤ (s0 * T0 - Q0) * Q1 * ((T1 * s0 + Q1) * T0 - T1 * (s0 * T0 - Q0)) := by
    have : (T1 * s0 + Q1) * T0 - T1 * (s0 * T0 - Q0) = T0 * Q1 + T1 * Q0 := by ring
    rw [this]; positivity
  have hge : (s0 * T0 - Q0) * T1 ≤ C * T0 * (T1 * s0 + Q1) := by
    rw [← hid] at hpos
    have := nonneg_of_mul_nonneg_left hpos hD
    linarith
  have h1 : (s0 * T0 - Q0) * T1 * R2 ≤ C * T0 * (T1 * s0 + Q1) * R2 :=
    mul_le_mul_of_nonneg_right hge hR2.le
  have h2 : C * T0 * (T1 * s0 + Q1) * R2 < R1 * T0 * (T1 * s0 + Q1) := by
    have : 0 < T0 * (T1 * s0 + Q1) := by positivity
    nlinarith
  linarith

end SurgeT3Alg

namespace SurgeT3Aux
open DriverSurge.IC

open DriverSurge.IC

lemma other0 : other 0 = 1 := by decide
lemma other1 : other 1 = 0 := by decide

lemma S_pos (P : Primitives) (i : Fin 2) : 0 < P.sw i + P.sw (other i) :=
  add_pos (P.sw_pos i) (P.sw_pos _)

lemma q_nonneg (P : Primitives) (i : Fin 2) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ q P i τ := by
  unfold q
  have hS := S_pos P i
  apply mul_nonneg (div_nonneg (P.sw_pos i).le hS.le)
  have : Real.exp (-(P.sw i + P.sw (other i)) * τ) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  linarith

lemma q_pos (P : Primitives) (i : Fin 2) {τ : ℝ} (hτ : 0 < τ) : 0 < q P i τ := by
  unfold q
  have hS := S_pos P i
  apply mul_pos (div_pos (P.sw_pos i) hS)
  have : Real.exp (-(P.sw i + P.sw (other i)) * τ) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
  linarith

lemma q_le (P : Primitives) (i : Fin 2) {τ : ℝ} (hτ : 0 ≤ τ) : q P i τ ≤ P.sw i * τ := by
  unfold q
  have hS := S_pos P i
  have h1 := Real.add_one_le_exp (-(P.sw i + P.sw (other i)) * τ)
  have h2 : 1 - Real.exp (-(P.sw i + P.sw (other i)) * τ) ≤ (P.sw i + P.sw (other i)) * τ := by
    linarith
  calc P.sw i / (P.sw i + P.sw (other i)) * (1 - Real.exp (-(P.sw i + P.sw (other i)) * τ))
      ≤ P.sw i / (P.sw i + P.sw (other i)) * ((P.sw i + P.sw (other i)) * τ) :=
        mul_le_mul_of_nonneg_left h2 (div_nonneg (P.sw_pos i).le hS.le)
    _ = P.sw i * τ := by field_simp

lemma q_cont (P : Primitives) (i : Fin 2) : Continuous (q P i) := by
  unfold q; fun_prop

lemma int_id (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ) :
    IntegrableOn (fun τ : ℝ => τ) s (P.F i) := (hmean i).integrableOn

lemma int_q (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ)
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    IntegrableOn (q P i) s (P.F i) := by
  have hb : IntegrableOn (fun τ : ℝ => P.sw i * τ) s (P.F i) := (int_id P hmean i s).const_mul _
  refine Integrable.mono' hb (q_cont P i).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hs] with τ hτ
  have h0 : 0 ≤ τ := le_of_lt (hs0 hτ)
  rw [Real.norm_eq_abs, abs_of_nonneg (q_nonneg P i h0)]
  exact q_le P i h0

lemma int_price (P : Primitives) (hmean : FiniteMean P) (m z : Fin 2 → ℝ) (i : Fin 2)
    (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    IntegrableOn (price P m z i) s (P.F i) := by
  unfold price
  exact ((int_id P hmean i s).const_mul _).add ((int_q P hmean i s hs hs0).const_mul _)

lemma Wn_price (P : Primitives) (hmean : FiniteMean P) (m z : Fin 2 → ℝ) (i : Fin 2)
    (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    Wn P i (price P m z i) s = P.lam i * (m i * ∫ τ in s, τ ∂P.F i + z i * ∫ τ in s, q P i τ ∂P.F i) := by
  unfold Wn price
  rw [integral_add ((int_id P hmean i s).const_mul _) ((int_q P hmean i s hs hs0).const_mul _),
    integral_const_mul, integral_const_mul]

lemma x_nonneg (P : Primitives) (i : Fin 2) (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    0 ≤ ∫ τ in s, τ ∂P.F i :=
  setIntegral_nonneg hs (fun τ hτ => le_of_lt (hs0 hτ))

lemma y_nonneg (P : Primitives) (i : Fin 2) (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    0 ≤ ∫ τ in s, q P i τ ∂P.F i :=
  setIntegral_nonneg hs (fun τ hτ => q_nonneg P i (le_of_lt (hs0 hτ)))

lemma x_le (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) :
    ∫ τ in s, τ ∂P.F i ≤ ∫ τ in Ioi 0, τ ∂P.F i := by
  apply setIntegral_mono_set (int_id P hmean i _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    exact le_of_lt hτ
  · exact hs0.eventuallyLE

lemma x_diff (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) :
    ∫ τ in Ioi 0, τ ∂P.F i - ∫ τ in s, τ ∂P.F i = ∫ τ in Ioi 0 \ s, τ ∂P.F i := by
  rw [setIntegral_sdiff hs (int_id P hmean i _) hs0]

lemma pos_of_measure (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (t : Set ℝ)
    (ht : MeasurableSet t) (ht0 : t ⊆ Ioi 0) (hF : P.F i t ≠ 0) :
    0 < ∫ τ in t, τ ∂P.F i := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : t ⊆ Function.support (fun τ : ℝ => τ) ∩ t := fun τ hτ =>
      ⟨ne_of_gt (ht0 hτ), hτ⟩
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hF) (measure_mono this)
  · filter_upwards [ae_restrict_mem ht] with τ hτ
    exact le_of_lt (ht0 hτ)
  · exact int_id P hmean i t

lemma posy_of_measure (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (t : Set ℝ)
    (ht : MeasurableSet t) (ht0 : t ⊆ Ioi 0) (hF : P.F i t ≠ 0) :
    0 < ∫ τ in t, q P i τ ∂P.F i := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : t ⊆ Function.support (q P i) ∩ t := fun τ hτ =>
      ⟨ne_of_gt (q_pos P i (ht0 hτ)), hτ⟩
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hF) (measure_mono this)
  · filter_upwards [ae_restrict_mem ht] with τ hτ
    exact q_nonneg P i (le_of_lt (ht0 hτ))
  · exact int_q P hmean i t ht ht0

lemma F_Ioi (P : Primitives) (i : Fin 2) : P.F i (Ioi 0) ≠ 0 := by
  have := P.prob i
  intro h
  have h1 : P.F i univ ≤ P.F i (Iic 0) + P.F i (Ioi 0) := by
    rw [← Iic_union_Ioi]; exact measure_union_le _ _
  rw [P.support i, h, measure_univ] at h1
  simp at h1

lemma y_le (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) :
    ∫ τ in Ioi 0, q P i τ ∂P.F i ≤ P.sw i * ∫ τ in Ioi 0, τ ∂P.F i := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on (int_q P hmean i _ measurableSet_Ioi subset_rfl)
    ((int_id P hmean i _).const_mul _) measurableSet_Ioi
  intro τ hτ; exact q_le P i (le_of_lt hτ)



lemma Tn_pos (P : Primitives) (i : Fin 2) (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    0 < Tn P i s := by
  unfold Tn
  have := x_nonneg P i s hs hs0
  have := (P.lam_pos i).le
  positivity

lemma Qn_pos (P : Primitives) (i : Fin 2) (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    0 < Qn P i s := by
  unfold Qn
  have := y_nonneg P i s hs hs0
  have := (P.lam_pos i).le
  have := P.sw_pos i
  positivity

lemma reward_sub (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (g d : ℝ) :
    rewardCF P w σ - g =
      (Qn P 1 (σ 1) * (Wn P 0 (w 0) (σ 0) - g * Tn P 0 (σ 0) - d * Qn P 0 (σ 0)) +
        Qn P 0 (σ 0) * (Wn P 1 (w 1) (σ 1) - g * Tn P 1 (σ 1) + d * Qn P 1 (σ 1))) /
      (Tn P 1 (σ 1) * Qn P 0 (σ 0) + Tn P 0 (σ 0) * Qn P 1 (σ 1)) := by
  have hT0 := Tn_pos P 0 (σ 0) (hσ 0).1.measurableSet (hσ 0).2
  have hT1 := Tn_pos P 1 (σ 1) (hσ 1).1.measurableSet (hσ 1).2
  have hQ0 := Qn_pos P 0 (σ 0) (hσ 0).1.measurableSet (hσ 0).2
  have hQ1 := Qn_pos P 1 (σ 1) (hσ 1).1.measurableSet (hσ 1).2
  unfold rewardCF
  simp only [Fin.sum_univ_two, mu, stateRate, other0, other1]
  have h1 : 0 < Tn P 1 (σ 1) * Qn P 0 (σ 0) + Tn P 0 (σ 0) * Qn P 1 (σ 1) := by positivity
  have h2 : 0 < Tn P 0 (σ 0) * Qn P 1 (σ 1) + Tn P 1 (σ 1) * Qn P 0 (σ 0) := by positivity
  field_simp
  ring

lemma reward_le_of_cert (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ)
    (hσ : IsPolicy σ) (g d : ℝ)
    (h0 : Wn P 0 (w 0) (σ 0) - g * Tn P 0 (σ 0) - d * Qn P 0 (σ 0) ≤ 0)
    (h1 : Wn P 1 (w 1) (σ 1) - g * Tn P 1 (σ 1) + d * Qn P 1 (σ 1) ≤ 0) :
    rewardCF P w σ ≤ g ∧
    ((Wn P 0 (w 0) (σ 0) - g * Tn P 0 (σ 0) - d * Qn P 0 (σ 0) < 0 ∨
      Wn P 1 (w 1) (σ 1) - g * Tn P 1 (σ 1) + d * Qn P 1 (σ 1) < 0) → rewardCF P w σ < g) ∧
    ((Wn P 0 (w 0) (σ 0) - g * Tn P 0 (σ 0) - d * Qn P 0 (σ 0) = 0 ∧
      Wn P 1 (w 1) (σ 1) - g * Tn P 1 (σ 1) + d * Qn P 1 (σ 1) = 0) → rewardCF P w σ = g) := by
  have hT0 := Tn_pos P 0 (σ 0) (hσ 0).1.measurableSet (hσ 0).2
  have hT1 := Tn_pos P 1 (σ 1) (hσ 1).1.measurableSet (hσ 1).2
  have hQ0 := Qn_pos P 0 (σ 0) (hσ 0).1.measurableSet (hσ 0).2
  have hQ1 := Qn_pos P 1 (σ 1) (hσ 1).1.measurableSet (hσ 1).2
  have e := reward_sub P w σ hσ g d
  have hden : 0 < Tn P 1 (σ 1) * Qn P 0 (σ 0) + Tn P 0 (σ 0) * Qn P 1 (σ 1) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have : rewardCF P w σ - g ≤ 0 := by
      rw [e]; apply div_nonpos_of_nonpos_of_nonneg _ hden.le
      have := mul_nonpos_of_nonneg_of_nonpos hQ1.le h0
      have := mul_nonpos_of_nonneg_of_nonpos hQ0.le h1
      linarith
    linarith
  · intro h
    have : rewardCF P w σ - g < 0 := by
      rw [e]; apply div_neg_of_neg_of_pos _ hden
      rcases h with h | h
      · have := mul_neg_of_pos_of_neg hQ1 h
        have := mul_nonpos_of_nonneg_of_nonpos hQ0.le h1
        linarith
      · have := mul_nonpos_of_nonneg_of_nonpos hQ1.le h0
        have := mul_neg_of_pos_of_neg hQ0 h
        linarith
    linarith
  · rintro ⟨ha, hb⟩
    have : rewardCF P w σ - g = 0 := by rw [e, ha, hb]; simp
    linarith

lemma cert0_eq (P : Primitives) (hmean : FiniteMean P) (m z : Fin 2 → ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) (g d : ℝ) :
    Wn P 0 (price P m z 0) s - g * Tn P 0 s - d * Qn P 0 s =
      P.lam 0 * ((m 0 - g) * (∫ τ in s, τ ∂P.F 0) + (z 0 - d) * ∫ τ in s, q P 0 τ ∂P.F 0) -
        g - d * P.sw 0 := by
  rw [Wn_price P hmean m z 0 s hs hs0]; unfold Tn Qn; ring

lemma cert1_eq (P : Primitives) (hmean : FiniteMean P) (m z : Fin 2 → ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) (g d : ℝ) :
    Wn P 1 (price P m z 1) s - g * Tn P 1 s + d * Qn P 1 s =
      P.lam 1 * ((m 1 - g) * (∫ τ in s, τ ∂P.F 1) + (z 1 + d) * ∫ τ in s, q P 1 τ ∂P.F 1) -
        g + d * P.sw 1 := by
  rw [Wn_price P hmean m z 1 s hs hs0]; unfold Tn Qn; ring

lemma acceptAll_policy : IsPolicy acceptAll := fun _ => ⟨isOpen_Ioi, subset_rfl⟩

lemma lta_top : lowerThenAll ⊤ = acceptAll := by
  funext i; fin_cases i
  · ext τ; simp [lowerThenAll, acceptAll]
  · rfl

lemma lta_zero : lowerThenAll 0 = ![∅, Ioi 0] := by
  funext i; fin_cases i
  · ext τ
    simp only [lowerThenAll, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mem_setOf_eq,
      mem_empty_iff_false, iff_false, not_and, not_lt]
    intro h
    exact_mod_cast h.le
  · rfl

lemma lta_zero_policy : IsPolicy (lowerThenAll 0) := by
  rw [lta_zero]; intro i; fin_cases i
  · exact ⟨isOpen_empty, empty_subset _⟩
  · exact ⟨isOpen_Ioi, subset_rfl⟩

lemma price_meas (P : Primitives) (m z : Fin 2 → ℝ) (i : Fin 2) : Measurable (price P m z i) := by
  unfold price
  exact (continuous_const.mul continuous_id).add (continuous_const.mul (q_cont P i)) |>.measurable

lemma ae_rate (P : Primitives) (hmean : FiniteMean P) (m z : Fin 2 → ℝ) (σ : Fin 2 → Set ℝ)
    (hσ : IsPolicy σ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (i₀ : Fin 2)
    (X : Ω → Path) (hX : IsDriverModel P μ i₀ X) :
    ∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) = ((rewardCF P (price P m z) σ : ℝ) : EReal) :=
  lemma_1 P μ i₀ X hX (price P m z) σ hσ (price_meas P m z)
    (fun i => int_price P hmean m z i (σ i) (hσ i).1.measurableSet (hσ i).2)
    (fun i => int_id P hmean i (σ i))

lemma transfer (P : Primitives) (hmean : FiniteMean P) (m z : Fin 2 → ℝ) (σ σ' : Fin 2 → Set ℝ)
    (hσ : IsPolicy σ) (hσ' : IsPolicy σ') {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (i₀ : Fin 2) (X : Ω → Path) (hX : IsDriverModel P μ i₀ X) :
    (rewardCF P (price P m z) σ ≤ rewardCF P (price P m z) σ' →
      ∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) ≤ earningsRate (price P m z) σ' i₀ (X ω)) ∧
    (rewardCF P (price P m z) σ < rewardCF P (price P m z) σ' →
      ∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) < earningsRate (price P m z) σ' i₀ (X ω)) := by
  have h1 := ae_rate P hmean m z σ hσ μ i₀ X hX
  have h2 := ae_rate P hmean m z σ' hσ' μ i₀ X hX
  constructor
  · intro h
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, e2]; exact_mod_cast h
  · intro h
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, e2]; exact_mod_cast h

/-- facts about the accept-all integrals -/
lemma bar_facts (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) :
    0 < P.lam i * ∫ τ in Ioi 0, τ ∂P.F i ∧ 0 < P.lam i * ∫ τ in Ioi 0, q P i τ ∂P.F i ∧
    P.lam i * ∫ τ in Ioi 0, q P i τ ∂P.F i ≤ P.sw i * (P.lam i * ∫ τ in Ioi 0, τ ∂P.F i) ∧
    Tn P i (Ioi 0) = 1 + P.lam i * ∫ τ in Ioi 0, τ ∂P.F i ∧
    Qn P i (Ioi 0) = P.sw i + P.lam i * ∫ τ in Ioi 0, q P i τ ∂P.F i := by
  have hl := P.lam_pos i
  have hx := pos_of_measure P hmean i (Ioi 0) measurableSet_Ioi subset_rfl (F_Ioi P i)
  have hy := posy_of_measure P hmean i (Ioi 0) measurableSet_Ioi subset_rfl (F_Ioi P i)
  have hyl := y_le P hmean i
  refine ⟨mul_pos hl hx, mul_pos hl hy, ?_, rfl, rfl⟩
  have := mul_le_mul_of_nonneg_left hyl hl.le
  linarith

lemma ic_block (P : Primitives) (hmean : FiniteMean P) (R1 R2 : ℝ) (hR : R1 < R2)
    (H : (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) * Tn P 1 (Ioi 0) * R2 <
      R1 * Tn P 0 (Ioi 0) * (Tn P 1 (Ioi 0) * P.sw 0 + Qn P 1 (Ioi 0))) :
    ∃ m z : Fin 2 → ℝ, 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1 ∧
      stateRate P 0 (price P m z 0) (Ioi 0) = R1 ∧ stateRate P 1 (price P m z 1) (Ioi 0) = R2 ∧
      ∀ σ, IsPolicy σ → rewardCF P (price P m z) σ ≤ rewardCF P (price P m z) acceptAll ∧
        ((P.F 0 (Ioi 0 \ σ 0) ≠ 0 ∨ P.F 1 (Ioi 0 \ σ 1) ≠ 0) →
          rewardCF P (price P m z) σ < rewardCF P (price P m z) acceptAll) := by
  obtain ⟨hX0, hY0, hY0le, hT0, hQ0⟩ := bar_facts P hmean 0
  obtain ⟨hX1, hY1, hY1le, hT1, hQ1⟩ := bar_facts P hmean 1
  obtain ⟨g, δ, m0, m1, hg, hδ, hm0, hm1, ht0, ht1, he0, he1⟩ :=
    SurgeT3Alg.ic_alg (P.sw 0) (P.sw 1) _ _ _ _ _ _ _ _ R1 R2 (P.sw_pos 0) (P.sw_pos 1)
      hX0 hY0 hY0le hX1 hY1 hY1le hT0 hT1 hQ0 hQ1 hR H
  refine ⟨![m0, m1], ![-δ, δ], by simp; linarith, by simp; linarith, by simpa using hδ,
    ?_, ?_, ?_⟩
  · unfold stateRate
    rw [Wn_price P hmean _ _ 0 _ measurableSet_Ioi subset_rfl, ← ht0]
    simp only [Matrix.cons_val_zero]; ring
  · unfold stateRate
    rw [Wn_price P hmean _ _ 1 _ measurableSet_Ioi subset_rfl, ← ht1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  -- certificates
  have c0 : ∀ s, MeasurableSet s → s ⊆ Ioi 0 →
      Wn P 0 (price P ![m0, m1] ![-δ, δ] 0) s - g * Tn P 0 s - (-δ) * Qn P 0 s =
        P.lam 0 * (m0 - g) * ((∫ τ in s, τ ∂P.F 0) - ∫ τ in Ioi 0, τ ∂P.F 0) := by
    intro s hs hs0
    rw [cert0_eq P hmean _ _ s hs hs0]
    simp only [Matrix.cons_val_zero]
    linear_combination he0
  have c1 : ∀ s, MeasurableSet s → s ⊆ Ioi 0 →
      Wn P 1 (price P ![m0, m1] ![-δ, δ] 1) s - g * Tn P 1 s + (-δ) * Qn P 1 s =
        P.lam 1 * (m1 - g) * ((∫ τ in s, τ ∂P.F 1) - ∫ τ in Ioi 0, τ ∂P.F 1) := by
    intro s hs hs0
    rw [cert1_eq P hmean _ _ s hs hs0]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination he1
  have hall : rewardCF P (price P ![m0, m1] ![-δ, δ]) acceptAll = g := by
    refine (reward_le_of_cert P _ acceptAll acceptAll_policy g (-δ) ?_ ?_).2.2 ⟨?_, ?_⟩ <;>
      simp only [acceptAll]
    · rw [c0 _ measurableSet_Ioi subset_rfl]; simp
    · rw [c1 _ measurableSet_Ioi subset_rfl]; simp
    · rw [c0 _ measurableSet_Ioi subset_rfl]; simp
    · rw [c1 _ measurableSet_Ioi subset_rfl]; simp
  intro σ hσ
  have hs0m := (hσ 0).1.measurableSet
  have hs1m := (hσ 1).1.measurableSet
  have hl0 := P.lam_pos 0
  have hl1 := P.lam_pos 1
  have k0 : 0 < P.lam 0 * (m0 - g) := mul_pos hl0 (by linarith)
  have k1 : 0 < P.lam 1 * (m1 - g) := mul_pos hl1 (by linarith)
  have d0 := x_diff P hmean 0 (σ 0) hs0m (hσ 0).2
  have d1 := x_diff P hmean 1 (σ 1) hs1m (hσ 1).2
  have n0 : 0 ≤ ∫ τ in Ioi 0 \ σ 0, τ ∂P.F 0 :=
    x_nonneg P 0 _ (measurableSet_Ioi.diff hs0m) sdiff_subset
  have n1 : 0 ≤ ∫ τ in Ioi 0 \ σ 1, τ ∂P.F 1 :=
    x_nonneg P 1 _ (measurableSet_Ioi.diff hs1m) sdiff_subset
  have hc := reward_le_of_cert P _ σ hσ g (-δ)
    (by rw [c0 _ hs0m (hσ 0).2]; exact mul_nonpos_of_nonneg_of_nonpos k0.le (by linarith))
    (by rw [c1 _ hs1m (hσ 1).2]; exact mul_nonpos_of_nonneg_of_nonpos k1.le (by linarith))
  rw [hall]
  refine ⟨hc.1, fun hrej => hc.2.1 ?_⟩
  rcases hrej with h | h
  · left
    have := pos_of_measure P hmean 0 _ (measurableSet_Ioi.diff hs0m) sdiff_subset h
    rw [c0 _ hs0m (hσ 0).2]; exact mul_neg_of_pos_of_neg k0 (by linarith)
  · right
    have := pos_of_measure P hmean 1 _ (measurableSet_Ioi.diff hs1m) sdiff_subset h
    rw [c1 _ hs1m (hσ 1).2]; exact mul_neg_of_pos_of_neg k1 (by linarith)

lemma nonic_block (P : Primitives) (hmean : FiniteMean P) (R1 R2 : ℝ) (hR2 : 0 ≤ R2)
    (H : R1 * Tn P 0 (Ioi 0) * (Tn P 1 (Ioi 0) * P.sw 0 + Qn P 1 (Ioi 0)) ≤
      (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) * Tn P 1 (Ioi 0) * R2) :
    ∃ m z : Fin 2 → ℝ, 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1 ∧
      stateRate P 0 (price P m z 0) (Ioi 0) = R1 ∧ stateRate P 1 (price P m z 1) (Ioi 0) = R2 ∧
      ∀ σ, IsPolicy σ → rewardCF P (price P m z) σ ≤ rewardCF P (price P m z) (lowerThenAll 0) := by
  obtain ⟨hX0, hY0, hY0le, hT0, hQ0⟩ := bar_facts P hmean 0
  obtain ⟨hX1, hY1, hY1le, hT1, hQ1⟩ := bar_facts P hmean 1
  obtain ⟨g, u, z0, m1, hgu, hg, hu, hm1, hz0, ht0, ht1, he1⟩ :=
    SurgeT3Alg.nonic_alg (P.sw 0) (P.sw 1) _ _ _ _ _ _ _ _ R1 R2 (P.sw_pos 0) (P.sw_pos 1)
      hX0 hY0 hY0le hX1 hY1 hT0 hT1 hQ0 hQ1 hR2 H
  refine ⟨![g, m1], ![z0, u], by simpa using hg, by simp; linarith, by simpa using hu,
    ?_, ?_, ?_⟩
  · unfold stateRate
    rw [Wn_price P hmean _ _ 0 _ measurableSet_Ioi subset_rfl, ← ht0]
    simp only [Matrix.cons_val_zero]; ring
  · unfold stateRate
    rw [Wn_price P hmean _ _ 1 _ measurableSet_Ioi subset_rfl, ← ht1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  have c0 : ∀ s, MeasurableSet s → s ⊆ Ioi 0 →
      Wn P 0 (price P ![g, m1] ![z0, u] 0) s - g * Tn P 0 s - (-u) * Qn P 0 s =
        P.lam 0 * (z0 + u) * ∫ τ in s, q P 0 τ ∂P.F 0 := by
    intro s hs hs0
    rw [cert0_eq P hmean _ _ s hs hs0]
    simp only [Matrix.cons_val_zero]
    linear_combination hgu
  have c1 : ∀ s, MeasurableSet s → s ⊆ Ioi 0 →
      Wn P 1 (price P ![g, m1] ![z0, u] 1) s - g * Tn P 1 s + (-u) * Qn P 1 s =
        P.lam 1 * (m1 - g) * ((∫ τ in s, τ ∂P.F 1) - ∫ τ in Ioi 0, τ ∂P.F 1) := by
    intro s hs hs0
    rw [cert1_eq P hmean _ _ s hs hs0]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination he1
  have hstar : rewardCF P (price P ![g, m1] ![z0, u]) (lowerThenAll 0) = g := by
    have h00 : lowerThenAll 0 0 = ∅ := by rw [lta_zero]; rfl
    have h01 : lowerThenAll 0 1 = Ioi 0 := by rw [lta_zero]; rfl
    refine (reward_le_of_cert P _ _ lta_zero_policy g (-u) ?_ ?_).2.2 ⟨?_, ?_⟩
    · rw [h00, c0 _ MeasurableSet.empty (empty_subset _)]; simp
    · rw [h01, c1 _ measurableSet_Ioi subset_rfl]; simp
    · rw [h00, c0 _ MeasurableSet.empty (empty_subset _)]; simp
    · rw [h01, c1 _ measurableSet_Ioi subset_rfl]; simp
  intro σ hσ
  have hs0m := (hσ 0).1.measurableSet
  have hs1m := (hσ 1).1.measurableSet
  have hl0 := P.lam_pos 0
  have hl1 := P.lam_pos 1
  have k0 : P.lam 0 * (z0 + u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl0.le hz0
  have k1 : 0 ≤ P.lam 1 * (m1 - g) := mul_nonneg hl1.le (by linarith)
  have y0 := y_nonneg P 0 (σ 0) hs0m (hσ 0).2
  have x1 := x_le P hmean 1 (σ 1) hs1m (hσ 1).2
  have hc := reward_le_of_cert P _ σ hσ g (-u)
    (by rw [c0 _ hs0m (hσ 0).2]; exact mul_nonpos_of_nonpos_of_nonneg k0 y0)
    (by rw [c1 _ hs1m (hσ 1).2]; exact mul_nonpos_of_nonneg_of_nonpos k1 (by linarith))
  rw [hstar]; exact hc.1

end SurgeT3Aux

open DriverSurge.IC SurgeT3Aux

theorem solution (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (hmean : FiniteMean P) :
    (0 ≤ Cconst P ∧ Cconst P < 1) ∧
    (∀ R₁ R₂ : ℝ, R₁ < R₂ → 0 ≤ R₂ →
      ∃ m z : Fin 2 → ℝ, 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1 ∧
        stateRate P 0 (price P m z 0) (Ioi 0) = R₁ ∧ stateRate P 1 (price P m z 1) (Ioi 0) = R₂ ∧
        ∃ t₁ : EReal, 0 ≤ t₁ ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (i₀ : Fin 2) (X : Ω → Path),
            IsDriverModel P μ i₀ X → ∀ σ : Fin 2 → Set ℝ, IsPolicy σ →
              ∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) ≤
                earningsRate (price P m z) (lowerThenAll t₁) i₀ (X ω)) ∧
    (∀ R₁ R₂ : ℝ, R₁ < R₂ → 0 < R₂ → Cconst P < R₁ / R₂ → R₁ / R₂ < 1 →
      ∃ m z : Fin 2 → ℝ, 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1 ∧
        stateRate P 0 (price P m z 0) (Ioi 0) = R₁ ∧ stateRate P 1 (price P m z 1) (Ioi 0) = R₂ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (i₀ : Fin 2) (X : Ω → Path),
          IsDriverModel P μ i₀ X → ∀ σ : Fin 2 → Set ℝ, IsPolicy σ →
            (∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) ≤
              earningsRate (price P m z) acceptAll i₀ (X ω)) ∧
            ((P.F 0 (Ioi 0 \ σ 0) ≠ 0 ∨ P.F 1 (Ioi 0 \ σ 1) ≠ 0) →
              ∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) <
                earningsRate (price P m z) acceptAll i₀ (X ω))) := by
  obtain ⟨hX0, hY0, hY0le, hT0, hQ0⟩ := bar_facts P hmean 0
  obtain ⟨hX1, hY1, hY1le, hT1, hQ1⟩ := bar_facts P hmean 1
  have hT1p : 0 < Tn P 1 (Ioi 0) := Tn_pos P 1 _ measurableSet_Ioi subset_rfl
  have hQ1p : 0 < Qn P 1 (Ioi 0) := Qn_pos P 1 _ measurableSet_Ioi subset_rfl
  refine ⟨?_, ?_, ?_⟩
  · exact SurgeT3Alg.C_alg (P.sw 0) _ _ _ _ _ _ (P.sw_pos 0) hX0 hY0 hY0le hT0 hT1p hQ0 hQ1p
  · intro R₁ R₂ hR hR2
    by_cases H : (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) * Tn P 1 (Ioi 0) * R₂ <
        R₁ * Tn P 0 (Ioi 0) * (Tn P 1 (Ioi 0) * P.sw 0 + Qn P 1 (Ioi 0))
    · obtain ⟨m, z, h1, h2, h3, h4, h5, hopt⟩ := ic_block P hmean R₁ R₂ hR H
      refine ⟨m, z, h1, h2, h3, h4, h5, ⊤, le_top, ?_⟩
      intro Ω _ μ i₀ X hX σ hσ
      rw [lta_top]
      exact (transfer P hmean m z σ acceptAll hσ acceptAll_policy μ i₀ X hX).1 (hopt σ hσ).1
    · push Not at H
      obtain ⟨m, z, h1, h2, h3, h4, h5, hopt⟩ := nonic_block P hmean R₁ R₂ hR2 H
      refine ⟨m, z, h1, h2, h3, h4, h5, 0, le_rfl, ?_⟩
      intro Ω _ μ i₀ X hX σ hσ
      exact (transfer P hmean m z σ (lowerThenAll 0) hσ lta_zero_policy μ i₀ X hX).1 (hopt σ hσ)
  · intro R₁ R₂ hR hR2 hC _
    have H := SurgeT3Alg.C_H (P.sw 0) _ _ _ _ _ _ R₁ R₂ (P.sw_pos 0) hX0 hY0 hY0le hT0 hT1p hQ0 hQ1p
      hR2 hC
    obtain ⟨m, z, h1, h2, h3, h4, h5, hopt⟩ := ic_block P hmean R₁ R₂ hR H
    refine ⟨m, z, h1, h2, h3, h4, h5, ?_⟩
    intro Ω _ μ i₀ X hX σ hσ
    have tr := transfer P hmean m z σ acceptAll hσ acceptAll_policy μ i₀ X hX
    exact ⟨tr.1 (hopt σ hσ).1, fun hrej => tr.2 ((hopt σ hσ).2 hrej)⟩
