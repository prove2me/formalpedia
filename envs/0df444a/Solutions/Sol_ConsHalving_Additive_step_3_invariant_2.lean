-- Prove2me | solution 2 for ConsHalving.Additive.step_3_invariant
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:25:11.223729+00:00
-- url     : https://prove2.me/submissions/427da42b-547b-464b-b359-c97b5a135e62

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

set_option autoImplicit false
open ConsHalving.Additive

theorem ch_affine {n m : ℕ} (u : Fin n → Fin m → ℝ) (x y : Fin m → ℝ) (γ : ℝ)
    (hx : SolvesS u x) (hy : SolvesS u y) : SolvesS u (stepPoint x y γ) := by
  intro i
  have h1 := hx i
  have h2 := hy i
  have : ∑ j, (stepPoint x y γ j - 1/2) * u i j
      = (1-γ) * ∑ j, (x j - 1/2) * u i j + γ * ∑ j, (y j - 1/2) * u i j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [stepPoint]; ring
  rw [this, h1, h2]; ring
theorem ch_gamma_nonneg {m : ℕ} (x y : Fin m → ℝ) (hx : IsFractional x) (j : Fin m)
    (hne : y j ≠ x j) : 0 ≤ gamma x y j := by
  unfold gamma
  split_ifs with h
  · exact div_nonneg (by linarith [(hx j).2]) (by linarith)
  · have : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    exact div_nonneg (hx j).1 (by linarith)

theorem ch_step_mem {m : ℕ} (x y : Fin m → ℝ) (hx : IsFractional x) (j : Fin m)
    (hne : y j ≠ x j) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ gamma x y j) :
    0 ≤ stepPoint x y γ j ∧ stepPoint x y γ j ≤ 1 := by
  unfold gamma at h1
  unfold stepPoint
  have hxj := hx j
  split_ifs at h1 with h
  · have hpos : 0 < y j - x j := by linarith
    have := (le_div_iff₀ hpos).mp h1
    constructor <;> nlinarith [hxj.1, hxj.2, mul_nonneg h0 hpos.le]
  · have hlt : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    have hpos : 0 < x j - y j := by linarith
    have := (le_div_iff₀ hpos).mp h1
    constructor <;> nlinarith [hxj.1, hxj.2, mul_nonneg h0 hpos.le]

theorem ch_step_jstar {m : ℕ} (x y : Fin m → ℝ) (j : Fin m) (hne : y j ≠ x j) :
    stepPoint x y (gamma x y j) j = 0 ∨ stepPoint x y (gamma x y j) j = 1 := by
  unfold stepPoint gamma
  split_ifs with h
  · right
    have hd : y j - x j ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  · left
    have hlt : y j < x j := lt_of_le_of_ne (not_lt.mp h) hne
    have hd : x j - y j ≠ 0 := by linarith
    field_simp
    ring

theorem ch_3c {m : ℕ} (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsFractional x) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsFractional (stepPoint x y (gamma x y jstar)) ∧
      (∀ j, y j = x j → stepPoint x y (gamma x y jstar) j = x j) ∧
      (stepPoint x y (gamma x y jstar) jstar = 0 ∨
        stepPoint x y (gamma x y jstar) jstar = 1) := by
  have h0 : 0 ≤ gamma x y jstar := ch_gamma_nonneg x y hx jstar hstar
  have key : ∀ j, y j = x j → stepPoint x y (gamma x y jstar) j = x j := by
    intro j hj
    simp only [stepPoint, hj]
    ring
  refine ⟨fun j => ?_, key, ch_step_jstar x y jstar hstar⟩
  by_cases hne : y j = x j
  · rw [key j hne]
    exact hx j
  · exact ch_step_mem x y hx j hne _ h0 (hmin j hne)
theorem ch_solvesS_iff {n m : ℕ} (u : Fin n → Fin m → ℝ) (x : Fin m → ℝ) :
    SolvesS u x ↔ ∀ i, util u i x = util u i (fun j => 1 - x j) := by
  have key : ∀ i, util u i x - util u i (fun j => 1 - x j) = 2 * ∑ j, (x j - 1 / 2) * u i j := by
    intro i
    unfold util
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · intro h i
    have := key i
    rw [h i] at this
    linarith
  · intro h i
    have := key i
    rw [h i] at this
    linarith

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m))
    (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsConsensusHalving u x) (hT : ∀ j ∈ T, x j = 0 ∨ x j = 1)
    (hy : SolvesST u T x y) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsConsensusHalving u (stepPoint x y (gamma x y jstar)) ∧ jstar ∉ T ∧
      ∀ j ∈ insert jstar T,
        stepPoint x y (gamma x y jstar) j = 0 ∨ stepPoint x y (gamma x y jstar) j = 1 := by
  have hxS : SolvesS u x := (ch_solvesS_iff u x).2 hx.2
  have hsS : SolvesS u (stepPoint x y (gamma x y jstar)) := ch_affine u x y _ hxS hy.1
  have h3 := ch_3c x y jstar hx.1 hstar hmin
  have hnT : jstar ∉ T := fun h => hstar (hy.2 jstar h)
  refine ⟨⟨h3.1, (ch_solvesS_iff u _).1 hsS⟩, hnT, ?_⟩
  intro j hj
  rcases Finset.mem_insert.1 hj with h | h
  · rw [h]
    exact h3.2.2
  · rw [h3.2.1 j (hy.2 j h)]
    exact hT j h
