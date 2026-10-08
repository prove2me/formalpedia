-- Prove2me | solution 1 for DaiWeissFluid.ThreeBuffer.drift_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:40:30.82535+00:00
-- url     : https://prove2.me/submissions/37cf0f34-0744-463c-97ca-869e510c1245

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

set_option autoImplicit false

open DaiWeissFluid.ThreeBuffer in
theorem solution (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (Q T : ℝ → Fin 3 → ℝ)
    (hsol : (threeBuffer m).IsFluidSolution Q T) (t : ℝ) (ht : 0 ≤ t) (i : Fin 2) :
    lyap m Q i t =
      lyap m Q i 0 + t - (threeBuffer m).busy T i t / (threeBuffer m).ρ i := by
  have h0 := hsol.flow t ht 0
  have h1 := hsol.flow t ht 1
  have h2 := hsol.flow t ht 2
  simp only [ReentrantLine.inflow, ReentrantLine.μ, threeBuffer] at h0 h1 h2
  simp at h0 h1 h2
  have hm0 := hm 0
  have hm1 := hm 1
  have hm2 := hm 2
  have hB0 : (threeBuffer m).busy T 0 t = T t 0 + T t 2 := by
    simp only [ReentrantLine.busy, ReentrantLine.C]
    rw [Finset.sum_filter, Fin.sum_univ_three]; simp [threeBuffer]
  have hB1 : (threeBuffer m).busy T 1 t = T t 1 := by
    simp only [ReentrantLine.busy, ReentrantLine.C]
    rw [Finset.sum_filter, Fin.sum_univ_three]; simp [threeBuffer]
  have hR0 : (threeBuffer m).ρ 0 = m 0 + m 2 := by
    simp only [ReentrantLine.ρ, ReentrantLine.C]
    rw [Finset.sum_filter, Fin.sum_univ_three]; simp [threeBuffer]
  have hR1 : (threeBuffer m).ρ 1 = m 1 := by
    simp only [ReentrantLine.ρ, ReentrantLine.C]
    rw [Finset.sum_filter, Fin.sum_univ_three]; simp [threeBuffer]
  have hQ0 : ∀ s, Qplus Q 0 s = Q s 0 := by
    intro s; simp only [Qplus]; rw [Finset.sum_filter, Fin.sum_univ_three]; simp
  have hQ1 : ∀ s, Qplus Q 1 s = Q s 0 + Q s 1 := by
    intro s; simp only [Qplus]; rw [Finset.sum_filter, Fin.sum_univ_three]; simp
  have hQ2 : ∀ s, Qplus Q 2 s = Q s 0 + Q s 1 + Q s 2 := by
    intro s; simp only [Qplus]; rw [Finset.sum_filter, Fin.sum_univ_three]; simp
  have hne : m 0 + m 2 ≠ 0 := by linarith
  fin_cases i
  · show lyap m Q 0 t = lyap m Q 0 0 + t - (threeBuffer m).busy T 0 t / (threeBuffer m).ρ 0
    rw [hB0, hR0]
    simp only [lyap, Matrix.cons_val_zero, hQ0, hQ2, theta]
    rw [h0, h1, h2]
    field_simp
    ring
  · show lyap m Q 1 t = lyap m Q 1 0 + t - (threeBuffer m).busy T 1 t / (threeBuffer m).ρ 1
    rw [hB1, hR1]
    simp only [lyap, Matrix.cons_val_one, Matrix.cons_val_zero, hQ1]
    rw [h0, h1]
    field_simp
    ring
