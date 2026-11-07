-- Prove2me | solution 1 for DaiWeissFluid.LuKumar.priority_unstable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:47:40.806675+00:00
-- url     : https://prove2.me/submissions/21310484-eec0-4cc2-b826-5d552c54ad3b

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network
import Theorems.Thm_DaiWeissFluid_LuKumar_scaled_cycles

open DaiWeissFluid.LuKumar

theorem solution (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : 1 ≤ m 1 + m 3) :
    ¬ DaiWeissFluid.ThreeBuffer.FluidStable ((luKumar m).IsPrioritySolution piLK) := by
  rintro ⟨δ, hδ, h⟩
  obtain ⟨Q, T, hP, hQ0, hQs⟩ := scaled_cycles m hm h51₁ h51₂ h52
  have h1m : 0 < 1 - m 1 := by linarith [hm 2]
  have hr : 1 ≤ m 3 / (1 - m 1) := by rw [le_div_iff₀ h1m]; linarith
  set a := (m 1 + m 3) / (1 - m 1) with ha
  have hapos : 0 < a := by have := hm 1; have := hm 3; positivity
  obtain ⟨n, hn⟩ := exists_nat_ge (δ / a)
  have hs : (n : ℝ) * a ≤ ∑ j ∈ Finset.range n, (m 3 / (1 - m 1)) ^ j * a := by
    have : ∑ j ∈ Finset.range n, a ≤ ∑ j ∈ Finset.range n, (m 3 / (1 - m 1)) ^ j * a := by
      apply Finset.sum_le_sum
      intro j _
      have := one_le_pow₀ (n := j) hr
      nlinarith
    simpa using this
  have hδn : δ ≤ ∑ j ∈ Finset.range n, (m 3 / (1 - m 1)) ^ j * a := by
    have : δ ≤ n * a := by rwa [div_le_iff₀ hapos] at hn
    linarith
  have hsum : ∑ k, Q 0 k = 1 := by
    rw [hQ0]; simp [Fin.sum_univ_four]
  have hz := h Q T hP hsum _ hδn 0
  have hq := hQs n
  simp only at hq
  rw [hq] at hz
  have hpos : 0 < (m 3 / (1 - m 1)) ^ n := pow_pos (by linarith) n
  have : (![(m 3 / (1 - m 1)) ^ n, 0, 0, 0] : Fin 4 → ℝ) 0 = (m 3 / (1 - m 1)) ^ n := rfl
  rw [this] at hz
  exact hpos.ne' hz
