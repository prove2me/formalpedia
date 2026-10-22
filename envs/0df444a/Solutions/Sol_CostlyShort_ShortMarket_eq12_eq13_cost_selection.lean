-- Prove2me | solution 1 for CostlyShort.ShortMarket.eq12_eq13_cost_selection
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:11:15.029591+00:00
-- url     : https://prove2.me/submissions/b9228dab-e089-44a1-b482-41e62c307075

import Mathlib
import Definitions.Def_CostlyShort_ShortMarket_Setting

set_option autoImplicit false

open CostlyShort.ShortMarket

theorem solution (θ₁o θ₁p Wo Wp γ : ℝ)
    (hγ : 0 ≤ γ) (hWo : 0 ≤ Wo) (hWp : 0 < Wp) (h11 : 0 < θ₁o + γ) :
    {y | γ ≤ y ∧ ∀ z, γ ≤ z → lendingRevenue θ₁o θ₁p Wo Wp z ≤ lendingRevenue θ₁o θ₁p Wo Wp y} =
        (if 0 ≤ θ₁p + γ then Set.Ici γ else {max γ (-θ₁p / 2)}) ∧
      IsLeast {y | γ ≤ y ∧ ∀ z, γ ≤ z →
        lendingRevenue θ₁o θ₁p Wo Wp z ≤ lendingRevenue θ₁o θ₁p Wo Wp y} (max γ (-θ₁p / 2)) := by
  have hR : ∀ y, γ ≤ y → lendingRevenue θ₁o θ₁p Wo Wp y = Wp * (y * max (-(θ₁p + y)) 0) := by
    intro y hy
    unfold lendingRevenue
    have : max (-(θ₁o + y)) 0 = 0 := max_eq_right (by linarith)
    rw [this]; ring
  set M : Set ℝ := {y | γ ≤ y ∧ ∀ z, γ ≤ z →
    lendingRevenue θ₁o θ₁p Wo Wp z ≤ lendingRevenue θ₁o θ₁p Wo Wp y} with hM
  by_cases hc : 0 ≤ θ₁p + γ
  · -- the pessimist never shorts at admissible costs: revenue vanishes on [γ, ∞)
    have hzero : ∀ y, γ ≤ y → lendingRevenue θ₁o θ₁p Wo Wp y = 0 := by
      intro y hy
      rw [hR y hy, max_eq_right (by linarith : -(θ₁p + y) ≤ 0)]
      ring
    have hMeq : M = Set.Ici γ := by
      ext y
      constructor
      · exact fun h => h.1
      · intro hy
        exact ⟨hy, fun z hz => by rw [hzero z hz, hzero y hy]⟩
    have hmax : max γ (-θ₁p / 2) = γ := max_eq_left (by linarith)
    rw [if_pos hc, hMeq, hmax]
    exact ⟨rfl, isLeast_Ici⟩
  · push_neg at hc
    set y0 := max γ (-θ₁p / 2) with hy0
    have hθ : θ₁p < -γ := by linarith
    have hy0γ : γ ≤ y0 := le_max_left _ _
    have sB : ∀ z, γ ≤ z → z ≠ y0 →
        z * max (-(θ₁p + z)) 0 < y0 * max (-(θ₁p + y0)) 0 := by
      intro z hz hne
      rcases le_total γ (-θ₁p / 2) with hc2 | hc2
      · have hy : y0 = -θ₁p / 2 := max_eq_right hc2
        rw [hy] at hne ⊢
        have hpos : 0 ≤ -(θ₁p + -θ₁p / 2) := by linarith
        rw [max_eq_left hpos]
        rcases le_total 0 (-(θ₁p + z)) with hz2 | hz2
        · rw [max_eq_left hz2]
          have hne' : z + θ₁p / 2 ≠ 0 := fun h => hne (by linarith)
          have := lt_of_le_of_ne (sq_nonneg (z + θ₁p / 2)) (Ne.symm (pow_ne_zero 2 hne'))
          nlinarith
        · rw [max_eq_right hz2]
          nlinarith
      · have hy : y0 = γ := max_eq_left hc2
        rw [hy] at hne ⊢
        have hzγ : γ < z := lt_of_le_of_ne hz (Ne.symm hne)
        have hγpos : 0 < γ := by linarith
        have hpos : 0 ≤ -(θ₁p + γ) := by linarith
        rw [max_eq_left hpos]
        rcases le_total 0 (-(θ₁p + z)) with hz2 | hz2
        · rw [max_eq_left hz2]
          have h1 : 0 < z - γ := by linarith
          have h2 : 0 < θ₁p + γ + z := by linarith
          nlinarith [mul_pos h1 h2]
        · rw [max_eq_right hz2]
          have : 0 < γ * -(θ₁p + γ) := mul_pos hγpos (by linarith)
          linarith
    have hMeq : M = {y0} := by
      ext y
      constructor
      · rintro ⟨hy, hmax⟩
        by_contra hne
        have h1 := sB y hy hne
        have h2 := hmax y0 hy0γ
        rw [hR y0 hy0γ, hR y hy] at h2
        nlinarith
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        refine ⟨hy0γ, fun z hz => ?_⟩
        rw [hR z hz, hR y0 hy0γ]
        by_cases hzy : z = y0
        · rw [hzy]
        · have := sB z hz hzy
          nlinarith
    rw [if_neg (not_le.2 hc), hMeq]
    exact ⟨rfl, isLeast_singleton⟩
