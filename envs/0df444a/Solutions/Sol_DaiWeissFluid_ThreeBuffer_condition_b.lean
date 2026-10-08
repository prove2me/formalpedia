-- Prove2me | solution 1 for DaiWeissFluid.ThreeBuffer.condition_b
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:26:52.095972+00:00
-- url     : https://prove2.me/submissions/abc0d223-6edc-407f-9552-5df8563d63b6

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

open DaiWeissFluid.ThreeBuffer in
theorem DWF_cb_volume0 (m : Fin 3 → ℝ) (Q : ℝ → Fin 3 → ℝ) (t : ℝ) :
    (threeBuffer m).volume Q 0 t = m 0 * Q t 0 + m 2 * Q t 2 := by
  unfold ReentrantLine.volume ReentrantLine.C
  rw [Finset.sum_filter, Fin.sum_univ_three]
  simp [threeBuffer]

open DaiWeissFluid.ThreeBuffer in
theorem DWF_cb_volume1 (m : Fin 3 → ℝ) (Q : ℝ → Fin 3 → ℝ) (t : ℝ) :
    (threeBuffer m).volume Q 1 t = m 1 * Q t 1 := by
  unfold ReentrantLine.volume ReentrantLine.C
  rw [Finset.sum_filter, Fin.sum_univ_three]
  simp [threeBuffer]

open DaiWeissFluid.ThreeBuffer in
theorem DWF_cb_lyap0 (m : Fin 3 → ℝ) (Q : ℝ → Fin 3 → ℝ) (t : ℝ) :
    lyap m Q 0 t = theta m * Q t 0 + (1 - theta m) * (Q t 0 + Q t 1 + Q t 2) := by
  simp only [lyap, Qplus, Matrix.cons_val_zero]
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [Fin.le_def]

open DaiWeissFluid.ThreeBuffer in
theorem DWF_cb_lyap1 (m : Fin 3 → ℝ) (Q : ℝ → Fin 3 → ℝ) (t : ℝ) :
    lyap m Q 1 t = Q t 0 + Q t 1 := by
  simp only [lyap, Qplus, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [Finset.sum_filter, Fin.sum_univ_three]
  simp [Fin.le_def]

open DaiWeissFluid.ThreeBuffer in
theorem solution (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (Q T : ℝ → Fin 3 → ℝ)
    (hsol : (threeBuffer m).IsFluidSolution Q T) (t : ℝ) (ht : 0 ≤ t) :
    ((threeBuffer m).volume Q 0 t = 0 → lyap m Q 0 t ≤ lyap m Q 1 t) ∧
      ((threeBuffer m).volume Q 1 t = 0 → lyap m Q 1 t ≤ lyap m Q 0 t) := by
  have h0 := hsol.nonneg t ht 0
  have h1 := hsol.nonneg t ht 1
  have h2 := hsol.nonneg t ht 2
  have m0 := hm 0
  have m1 := hm 1
  have m2 := hm 2
  have hθ0 : 0 ≤ theta m := by unfold theta; positivity
  have hθ1 : theta m ≤ 1 := by
    unfold theta; rw [div_le_one (by linarith)]; linarith
  rw [DWF_cb_volume0, DWF_cb_volume1, DWF_cb_lyap0, DWF_cb_lyap1]
  refine ⟨fun hW => ?_, fun hW => ?_⟩
  · have hq0 : Q t 0 = 0 := by nlinarith [mul_nonneg m0.le h0, mul_nonneg m2.le h2]
    have hq2 : Q t 2 = 0 := by nlinarith [mul_nonneg m0.le h0, mul_nonneg m2.le h2]
    rw [hq0, hq2]; nlinarith
  · have hq1 : Q t 1 = 0 := by
      rcases mul_eq_zero.mp hW with h | h
      · linarith
      · exact h
    rw [hq1]; nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) h2]
