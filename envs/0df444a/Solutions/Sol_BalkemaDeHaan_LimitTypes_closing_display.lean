-- Prove2me | solution 1 for BalkemaDeHaan.LimitTypes.closing_display
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:37:19.211485+00:00
-- url     : https://prove2.me/submissions/3f1f066b-d7b8-4132-9d2d-b559744f8519

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology


namespace BalkemaDeHaan.LimitTypes

lemma one_sub_PiLaw (x : ℝ) : 1 - PiLaw x = if x < 0 then 1 else Real.exp (-x) := by
  unfold PiLaw; split_ifs <;> ring

lemma one_sub_PiDiscreteLaw (γ x : ℝ) :
    1 - PiDiscreteLaw γ x = if x < 0 then 1 else Real.exp (-γ * ((⌊1 + x⌋ : ℤ) : ℝ)) := by
  unfold PiDiscreteLaw; split_ifs <;> ring

lemma one_sub_GammaLaw (α x : ℝ) :
    1 - GammaLaw α x = if x < 0 then 1 else (1 + x) ^ (-α) := by
  unfold GammaLaw; split_ifs <;> ring

lemma one_sub_GammaDiscreteLaw (γ α x : ℝ) :
    1 - GammaDiscreteLaw γ α x =
      if x < 0 then 1 else Real.exp (-γ * ((⌊1 + α * Real.log (1 + x)⌋ : ℤ) : ℝ)) := by
  unfold GammaDiscreteLaw; split_ifs <;> ring

lemma pi_part (t : ℝ) (ht : 0 < t) : ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
    min 1 ((1 - PiLaw (B + x * A)) / (1 - PiLaw t)) = 1 - PiLaw x := by
  refine ⟨1, one_pos, t, fun x => ?_⟩
  simp only [one_sub_PiLaw, mul_one]
  rw [if_neg (not_lt.mpr ht.le)]
  by_cases hx : x < 0
  · rw [if_pos hx]
    by_cases htx : t + x < 0
    · rw [if_pos htx]
      apply min_eq_left
      rw [one_div, ← Real.exp_neg, neg_neg]
      exact Real.one_le_exp ht.le
    · rw [if_neg htx]
      apply min_eq_left
      rw [← Real.exp_sub]
      apply Real.one_le_exp
      linarith
  · rw [if_neg hx]
    have htx : ¬ t + x < 0 := by push_neg at hx ⊢; linarith
    rw [if_neg htx, ← Real.exp_sub, show -(t + x) - -t = -x by ring]
    apply min_eq_right
    rw [Real.exp_le_one_iff]
    push_neg at hx; linarith

lemma pid_part (γ : ℝ) (hγ : 0 < γ) (t : ℝ) (ht : 0 < t) : ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
    min 1 ((1 - PiDiscreteLaw γ (B + x * A)) / (1 - PiDiscreteLaw γ t)) =
      1 - PiDiscreteLaw γ x := by
  set k : ℤ := ⌊1 + t⌋ with hk
  have hk1 : (1 : ℤ) ≤ k := by rw [hk, Int.le_floor]; push_cast; linarith
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  clear_value k
  refine ⟨1, one_pos, (k : ℝ), fun x => ?_⟩
  simp only [one_sub_PiDiscreteLaw, mul_one]
  rw [if_neg (not_lt.mpr ht.le), ← hk]
  have hfl : ⌊1 + ((k : ℝ) + x)⌋ = ⌊1 + x⌋ + k := by
    rw [show 1 + ((k : ℝ) + x) = (1 + x) + (k : ℝ) by ring, Int.floor_add_intCast]
  by_cases hx : x < 0
  · rw [if_pos hx]
    by_cases hkx : (k : ℝ) + x < 0
    · rw [if_pos hkx]
      apply min_eq_left
      rw [one_div, ← Real.exp_neg]
      apply Real.one_le_exp
      nlinarith
    · rw [if_neg hkx, hfl, ← Real.exp_sub]
      apply min_eq_left
      apply Real.one_le_exp
      have h0 : ⌊1 + x⌋ ≤ 0 := by
        have : ⌊1 + x⌋ < 1 := by rw [Int.floor_lt]; push_cast; linarith
        omega
      have h0' : ((⌊1 + x⌋ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h0
      push_cast
      nlinarith
  · rw [if_neg hx]
    have hkx : ¬ (k : ℝ) + x < 0 := by push_neg at hx ⊢; linarith
    rw [if_neg hkx, hfl, ← Real.exp_sub,
      show -γ * ((⌊1 + x⌋ + k : ℤ) : ℝ) - -γ * (k : ℝ) = -γ * ((⌊1 + x⌋ : ℤ) : ℝ) by
        push_cast; ring]
    apply min_eq_right
    rw [Real.exp_le_one_iff]
    have h1 : (1 : ℤ) ≤ ⌊1 + x⌋ := by rw [Int.le_floor]; push_cast; push_neg at hx; linarith
    have h1' : (1 : ℝ) ≤ ((⌊1 + x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast
    nlinarith

lemma gamma_part (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 < t) : ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
    min 1 ((1 - GammaLaw α (B + x * A)) / (1 - GammaLaw α t)) = 1 - GammaLaw α x := by
  refine ⟨1 + t, by linarith, t, fun x => ?_⟩
  simp only [one_sub_GammaLaw]
  rw [if_neg (not_lt.mpr ht.le)]
  have h1t : (0:ℝ) < 1 + t := by linarith
  have hprod : 1 + (t + x * (1 + t)) = (1 + t) * (1 + x) := by ring
  have hpos : 0 < (1 + t) ^ (-α) := Real.rpow_pos_of_pos h1t _
  by_cases hu : t + x * (1 + t) < 0
  · rw [if_pos hu]
    have hx : x < 0 := by
      by_contra h; push_neg at h
      nlinarith
    rw [if_pos hx]
    apply min_eq_left
    rw [one_div, ← Real.rpow_neg h1t.le, neg_neg]
    exact Real.one_le_rpow (by linarith) hα.le
  · rw [if_neg hu]
    have hx1 : 0 < 1 + x := by
      push_neg at hu
      by_contra h; push_neg at h
      nlinarith
    rw [hprod, Real.mul_rpow h1t.le hx1.le, mul_div_cancel_left₀ _ hpos.ne']
    by_cases hx : x < 0
    · rw [if_pos hx]
      apply min_eq_left
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 (by linarith) (by linarith)
    · rw [if_neg hx]
      apply min_eq_right
      exact Real.rpow_le_one_of_one_le_of_nonpos (by push_neg at hx; linarith) (by linarith)

lemma gammad_part (γ : ℝ) (hγ : 0 < γ) (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 < t) :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
    min 1 ((1 - GammaDiscreteLaw γ α (B + x * A)) / (1 - GammaDiscreteLaw γ α t)) =
      1 - GammaDiscreteLaw γ α x := by
  set k : ℤ := ⌊1 + α * Real.log (1 + t)⌋ with hk
  have hlogt : 0 < Real.log (1 + t) := Real.log_pos (by linarith)
  have hk1 : (1 : ℤ) ≤ k := by rw [hk, Int.le_floor]; push_cast; nlinarith
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  clear_value k
  set c : ℝ := Real.exp ((k : ℝ) / α) with hc
  have hc1 : 1 ≤ c := Real.one_le_exp (by positivity)
  have hc0 : 0 < c := by linarith
  clear_value c
  refine ⟨c, hc0, c - 1, fun x => ?_⟩
  simp only [one_sub_GammaDiscreteLaw]
  rw [if_neg (not_lt.mpr ht.le), ← hk]
  have hprod : 1 + (c - 1 + x * c) = c * (1 + x) := by ring
  by_cases hu : c - 1 + x * c < 0
  · rw [if_pos hu]
    have hx : x < 0 := by
      by_contra h; push_neg at h
      nlinarith
    rw [if_pos hx]
    apply min_eq_left
    rw [one_div, ← Real.exp_neg]
    apply Real.one_le_exp
    nlinarith
  · rw [if_neg hu]
    have hx1 : 0 < 1 + x := by
      push_neg at hu
      by_contra h; push_neg at h
      nlinarith
    have hfl : ⌊1 + α * Real.log (1 + (c - 1 + x * c))⌋ = ⌊1 + α * Real.log (1 + x)⌋ + k := by
      rw [hprod, Real.log_mul hc0.ne' hx1.ne', hc, Real.log_exp,
        show 1 + α * ((k:ℝ) / α + Real.log (1 + x)) = (1 + α * Real.log (1 + x)) + (k : ℝ) by
          field_simp; ring]
      exact Int.floor_add_intCast _ _
    rw [hfl, ← Real.exp_sub]
    by_cases hx : x < 0
    · rw [if_pos hx]
      apply min_eq_left
      apply Real.one_le_exp
      have hlog : Real.log (1 + x) < 0 := Real.log_neg hx1 (by linarith)
      have h0 : ⌊1 + α * Real.log (1 + x)⌋ ≤ 0 := by
        have : ⌊1 + α * Real.log (1 + x)⌋ < 1 := by rw [Int.floor_lt]; push_cast; nlinarith
        omega
      have h0' : ((⌊1 + α * Real.log (1 + x)⌋ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h0
      push_cast
      nlinarith
    · rw [if_neg hx]
      rw [show -γ * ((⌊1 + α * Real.log (1 + x)⌋ + k : ℤ) : ℝ) - -γ * (k : ℝ)
          = -γ * ((⌊1 + α * Real.log (1 + x)⌋ : ℤ) : ℝ) by push_cast; ring]
      apply min_eq_right
      rw [Real.exp_le_one_iff]
      have hlog : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by push_neg at hx; linarith)
      have h1 : (1 : ℤ) ≤ ⌊1 + α * Real.log (1 + x)⌋ := by
        rw [Int.le_floor]; push_cast; nlinarith
      have h1' : (1 : ℝ) ≤ ((⌊1 + α * Real.log (1 + x)⌋ : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast
      nlinarith

theorem closing_display_core :
    (∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - PiLaw (B + x * A)) / (1 - PiLaw t)) = 1 - PiLaw x) ∧
    (∀ γ : ℝ, 0 < γ → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - PiDiscreteLaw γ (B + x * A)) / (1 - PiDiscreteLaw γ t)) =
        1 - PiDiscreteLaw γ x) ∧
    (∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - GammaLaw α (B + x * A)) / (1 - GammaLaw α t)) = 1 - GammaLaw α x) ∧
    (∀ γ : ℝ, 0 < γ → ∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - GammaDiscreteLaw γ α (B + x * A)) / (1 - GammaDiscreteLaw γ α t)) =
        1 - GammaDiscreteLaw γ α x) :=
  ⟨fun t ht => pi_part t ht, fun γ hγ t ht => pid_part γ hγ t ht,
   fun α hα t ht => gamma_part α hα t ht, fun γ hγ α hα t ht => gammad_part γ hγ α hα t ht⟩

end BalkemaDeHaan.LimitTypes

open BalkemaDeHaan.LimitTypes


theorem solution :
    (∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - PiLaw (B + x * A)) / (1 - PiLaw t)) = 1 - PiLaw x) ∧
    (∀ γ : ℝ, 0 < γ → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - PiDiscreteLaw γ (B + x * A)) / (1 - PiDiscreteLaw γ t)) =
        1 - PiDiscreteLaw γ x) ∧
    (∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - GammaLaw α (B + x * A)) / (1 - GammaLaw α t)) = 1 - GammaLaw α x) ∧
    (∀ γ : ℝ, 0 < γ → ∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - GammaDiscreteLaw γ α (B + x * A)) / (1 - GammaDiscreteLaw γ α t)) =
        1 - GammaDiscreteLaw γ α x) := by
  exact closing_display_core
