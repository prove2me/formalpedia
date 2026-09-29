-- Prove2me | solution 1 for ChanPangGQVI.Existence.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:32.81381+00:00
-- url     : https://prove2.me/submissions/f136f527-2444-49ee-957d-4eed567e9931

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_Coercivity

open scoped RealInnerProductSpace
open ChanPangGQVI.Existence

theorem solution {n : ℕ} (μ K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x0 : EuclideanSpace ℝ (Fin n)) (h : IsStronglyCopositiveAt μ K x0) :
    IsCoerciveAt μ K x0 := by
  obtain ⟨hx0, α, hα, y0, hy0, hcop⟩ := h
  intro M
  refine ⟨2 * ‖x0‖ + 1 + (4 * (‖y0‖ + |M| + ‖y0‖ * ‖x0‖ + 1)) / α, ?_⟩
  intro x hxK hR y hy
  have hc := hcop x hxK y hy
  have hdiv : 0 ≤ (4 * (‖y0‖ + |M| + ‖y0‖ * ‖x0‖ + 1)) / α := by positivity
  have hx0n : 0 ≤ ‖x0‖ := norm_nonneg x0
  have ht1 : (1 : ℝ) ≤ ‖x‖ := by linarith
  have ht2c : 2 * ‖x0‖ ≤ ‖x‖ := by linarith
  have hu0 : 0 ≤ ‖x - x0‖ := norm_nonneg _
  have hu1 : ‖x‖ - ‖x0‖ ≤ ‖x - x0‖ := norm_sub_norm_le x x0
  have hu2 : ‖x - x0‖ ≤ ‖x‖ + ‖x0‖ := norm_sub_le x x0
  have hhalf : ‖x‖ / 2 ≤ ‖x - x0‖ := by linarith
  have hsq : ‖x‖ ^ 2 / 4 ≤ ‖x - x0‖ ^ 2 := by nlinarith [hhalf, hu0]
  have hαsq : α * (‖x‖ ^ 2 / 4) ≤ α * ‖x - x0‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hα.le
  have hy0inner : -(‖y0‖ * ‖x - x0‖) ≤ ⟪y0, x - x0⟫ := by
    have hb := abs_real_inner_le_norm y0 (x - x0)
    have := abs_le.mp hb
    linarith [this.1]
  have hαR : α * (2 * ‖x0‖ + 1) + 4 * (‖y0‖ + |M| + ‖y0‖ * ‖x0‖ + 1) ≤ α * ‖x‖ := by
    have hmul := mul_le_mul_of_nonneg_left hR hα.le
    have e : α * (2 * ‖x0‖ + 1 + (4 * (‖y0‖ + |M| + ‖y0‖ * ‖x0‖ + 1)) / α)
        = α * (2 * ‖x0‖ + 1) + 4 * (‖y0‖ + |M| + ‖y0‖ * ‖x0‖ + 1) := by
      field_simp
    rw [e] at hmul
    exact hmul
  have hq : ‖y0‖ * ‖x0‖ + 1 ≤ α * ‖x‖ / 4 - ‖y0‖ - M := by
    have hM : M ≤ |M| := le_abs_self M
    have hpos : 0 ≤ α * (2 * ‖x0‖ + 1) := by positivity
    linarith
  have hqnn : (0 : ℝ) ≤ α * ‖x‖ / 4 - ‖y0‖ - M := by
    have : 0 ≤ ‖y0‖ * ‖x0‖ := mul_nonneg (norm_nonneg y0) hx0n
    linarith
  have hAt : (‖y0‖ * ‖x0‖ + 1) * 1 ≤ (α * ‖x‖ / 4 - ‖y0‖ - M) * ‖x‖ :=
    mul_le_mul hq ht1 zero_le_one hqnn
  have hdu : ‖y0‖ * ‖x - x0‖ ≤ ‖y0‖ * (‖x‖ + ‖x0‖) :=
    mul_le_mul_of_nonneg_left hu2 (norm_nonneg y0)
  have hsym : ⟪x - x0, y⟫ = ⟪y - y0, x - x0⟫ + ⟪y0, x - x0⟫ := by
    have h1 : ⟪y - y0, x - x0⟫ = ⟪y, x - x0⟫ - ⟪y0, x - x0⟫ := by rw [inner_sub_left]
    have h2 : ⟪x - x0, y⟫ = ⟪y, x - x0⟫ := real_inner_comm _ _
    rw [h1, h2]
    ring
  rw [hsym]
  nlinarith [hc, hy0inner, hαsq, hAt, hdu]
