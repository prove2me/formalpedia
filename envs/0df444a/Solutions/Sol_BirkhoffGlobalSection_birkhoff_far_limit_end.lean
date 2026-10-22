-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_limit_end
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T15:21:39.694293+00:00
-- url     : https://prove2.me/submissions/12b84063-3564-4908-b9d8-1a2b9e9cf3b1

import Definitions.Def_BirkhoffShootingArcs
import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_axis_exclusion

open BirkhoffGlobalSection Set

lemma relPos_eq' (μ : ℝ) (s : Phase) :
    relativePosition μ s 0 = 2 * (s 0 ^ 2 - s 1 ^ 2) ∧ relativePosition μ s 1 = 4 * s 0 * s 1 := by
  simp [relativePosition, leviCivitaPosition]

lemma z_zero_of_pos_zero (a b : ℝ) (h1 : 2 * (a ^ 2 - b ^ 2) = 0) (h2 : 4 * a * b = 0) :
    a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    have : a ^ 4 = 0 := by nlinarith [sq_nonneg (a * b)]
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  refine ⟨ha, ?_⟩
  rw [ha] at h1
  have : b ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (by norm_num) |>.1 this

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (T : ℝ) (hT : 0 < T)
    (hx0 : (x : Phase) 0 = 0) (hx1 : 0 < (x : Phase) 1)
    (hv : jacobiVelocity (leviCivitaToJacobi μ (x : Phase)) 1 < 0)
    (hcl : ∀ t ∈ Set.Ioo 0 T, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hvx : ∀ t ∈ Set.Ioo 0 T, 0 < jacobiVelocity (leviCivitaToJacobi μ ((φ t x : LeftEnergyState μ c) : Phase)) 0)
    (hP : ∀ t ∈ Set.Ioo 0 T, 0 < zNormSq ((φ t x : LeftEnergyState μ c) : Phase))
    (hX : relativePosition μ ((φ T x : LeftEnergyState μ c) : Phase) 0 = 0)
    (hY : relativePosition μ ((φ T x : LeftEnergyState μ c) : Phase) 1 ≤ 0)
    (hVxT : 0 ≤ jacobiVelocity (leviCivitaToJacobi μ ((φ T x : LeftEnergyState μ c) : Phase)) 0)
    (hno : ¬ ∃ τ : ℝ, IsFarShootingArc φ x τ) :
    (∀ t ∈ Set.Ioo 0 T, relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
    ((((φ T x : LeftEnergyState μ c) : Phase) 0 = 0 ∧ ((φ T x : LeftEnergyState μ c) : Phase) 1 = 0) ∨
      (relativePosition μ ((φ T x : LeftEnergyState μ c) : Phase) 1 < 0 ∧ jacobiVelocity (leviCivitaToJacobi μ ((φ T x : LeftEnergyState μ c) : Phase)) 0 = 0)) := by
  have hopen := birkhoff_far_axis_exclusion μ c hμ0 hμ1 hc φ hφ x T hT hx0 hx1 hv hcl hvx hP
  refine ⟨hopen, ?_⟩
  rcases eq_or_lt_of_le hY with h | h
  · left
    rw [(relPos_eq' μ _).1] at hX; rw [(relPos_eq' μ _).2] at h
    exact z_zero_of_pos_zero _ _ hX h
  · right
    refine ⟨h, ?_⟩
    rcases eq_or_lt_of_le hVxT with h' | h'
    · exact h'.symm
    · exfalso
      apply hno
      refine ⟨T, hT, hopen, h, hX, fun u hu => ?_⟩
      rcases eq_or_lt_of_le hu.2 with h'' | h''
      · rw [h'']; exact h'
      · exact hvx u ⟨hu.1, h''⟩
