-- Prove2me | solution 1 for ConsistentSubmodular.consecutiveIntervalGap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:41:34.098477+00:00
-- url     : https://prove2.me/submissions/eed96434-b9b1-43c6-bb6c-119c9fdf52f7

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveIntervals
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique
import Theorems.Thm_ConsistentSubmodular_Chains_qStar_eq_uOne
import Theorems.Thm_ConsistentSubmodular_Chains_isEqualizing_iff
import Theorems.Thm_ConsistentSubmodular_Chains_adaptivityGap_eq
import Theorems.Thm_ConsistentSubmodular_Chains_xiStar_le_adaptivityGap

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

/-- Existence in Proposition 1: `Ψ(1/2) = -83/16 < 0 < 24 = Ψ(1)`, so the
intermediate value theorem gives a root in `(1/2, 1)`. -/
theorem exists_psi_root : ∃ ξ : ℝ, 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0 := by
  have hsub := intermediate_value_Ioo (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi (1 / 2)) (psi 1) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hξ⟩ := hsub hmem
  exact ⟨ξ, h1, h2, hξ⟩

/-- The root of `Ψ` in `(1/2, 1)` is `ξ⋆`. -/
theorem eq_xiStar {ξ : ℝ} (h₁ : 1 / 2 < ξ) (h₂ : ξ < 1) (hψ : psi ξ = 0) : ξ = xiStar := by
  have hset : {ξ : ℝ | 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0} = {ξ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, hx₂, hx⟩
      exact psi_root_unique hx₁ hx₂ h₁ h₂ hx hψ
    · rintro rfl
      exact ⟨h₁, h₂, hψ⟩
  rw [xiStar, hset, csSup_singleton]

/-- `ξ⋆` is the root of `Ψ` in `(1/2, 1)`. -/
theorem xiStar_root : 1 / 2 < xiStar ∧ xiStar < 1 ∧ psi xiStar = 0 := by
  obtain ⟨ξ, h1, h2, hψ⟩ := exists_psi_root
  have h := eq_xiStar h1 h2 hψ
  subst h
  exact ⟨h1, h2, hψ⟩

theorem xiStar_pos : 0 < xiStar := by linarith [xiStar_root.1]

theorem xiStar_eq_qStar : xiStar = 1 / (1 + qStar) := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

/-- The root of `Φ` in `[0, 1]` is unique. -/
theorem eq_uOne {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) (hx : phi x = 0) : x = uOne :=
  phi_strictAntiOn.injOn ⟨h₀, h₁⟩ ⟨uOne_pos.le, uOne_lt_one.le⟩ (hx.trans phi_uOne.symm)

/-- `ξ⋆ = 1 / (1 + u₁ u₂)` with `u₂ = u₁² (1 + u₁)`. -/
theorem xiStar_eq_uOne : xiStar = 1 / (1 + uOne ^ 3 * (1 + uOne)) := by
  rw [xiStar_eq_qStar, qStar_eq_uOne]

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem sum_Iic_eq {N : ℕ} (f : Fin (N + 1) → ℝ) (j : Fin (N + 1)) :
    ∑ i ∈ Finset.Iic j, f i = ∑ i, if i ≤ j then f i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem extremalInstance_consecutive : extremalInstance.IsNonincreasingConsecutive := by
  have h0 := uOne_pos
  have hb := uOne_bounds
  have hu2 : 0 < uOne ^ 2 * (1 + uOne) := by positivity
  refine ⟨by simp [extremalInstance], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp [extremalInstance]
    · simp [extremalInstance]
  · intro i
    fin_cases i
    · simp [extremalInstance]
      linarith
    · simp [extremalInstance]
      nlinarith
  · simp [extremalInstance]
    exact hu2

/-- The probabilities `(u₂, u₂/u₁ - u₂, 1 - u₂/u₁)` have the cumulative sums (5), so
they are the equalizing distribution of the three intervals. -/
theorem extremalInstance_equalizing : extremalInstance.IsEqualizing := by
  have h0 := uOne_pos
  rw [isEqualizing_iff extremalInstance_consecutive]
  intro j
  rw [sum_Iic_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, intervalLength]
  fin_cases j
  · simp [extremalInstance]
  · simp [extremalInstance, uTwo_div_uOne]
  · simp [extremalInstance, uTwo_div_uOne]
    field_simp

theorem extremalInstance_gap : extremalInstance.adaptivityGap = xiStar := by
  have h0 := uOne_pos
  have hphi := phi_uOne
  unfold phi at hphi
  have hB : ∑ j, extremalInstance.prob j * extremalInstance.left j =
      (uOne * (1 + uOne) - uOne ^ 2 * (1 + uOne)) + (1 - uOne * (1 + uOne)) * (1 + uOne) := by
    simp [Fin.sum_univ_succ, extremalInstance, uTwo_div_uOne]
  have hC : ∑ j, extremalInstance.prob j * intervalLength extremalInstance j =
      uOne ^ 2 * (1 + uOne) + (uOne * (1 + uOne) - uOne ^ 2 * (1 + uOne)) * uOne +
        (1 - uOne * (1 + uOne)) * (uOne ^ 2 * (1 + uOne)) := by
    simp [Fin.sum_univ_succ, extremalInstance, intervalLength, uTwo_div_uOne]
    ring
  have hdN : intervalLength extremalInstance (Fin.last 2) = uOne ^ 2 * (1 + uOne) := by
    simp [intervalLength, extremalInstance]
  rw [adaptivityGap_eq extremalInstance_consecutive extremalInstance_equalizing, xiStar_eq_uOne, hB, hC, hdN,
    div_eq_div_iff (by nlinarith [uOne_bounds]) (by positivity)]
  linear_combination (-(uOne ^ 2 * (1 + uOne))) * hphi

/-- **Lemma 4**: every instance of nonincreasing consecutive intervals with the
equalizing distribution has `Γ ≥ ξ⋆`, with equality for the three intervals
`[0, 1]`, `[1, 1 + u₁]`, `[1 + u₁, 1 + u₁ + u₂]`. -/
theorem consecutiveIntervalGap : ConsecutiveIntervalGapGoal :=
  ⟨fun _ _ hI hE => xiStar_le_adaptivityGap hI hE, uOne, uOne ^ 2 * (1 + uOne), uOne_pos,
    uOne_lt_one, phi_uOne, fun _ hx0 hx1 hx => eq_uOne hx0.le hx1.le hx, rfl, extremalInstance,
    extremalInstance_consecutive, extremalInstance_equalizing, extremalInstance_gap, rfl, rfl,
    rfl⟩

end ConsistentSubmodular.Chains

end

end

section

open ConsistentSubmodular

theorem solution : ConsecutiveIntervalGapGoal :=
  Chains.consecutiveIntervalGap

end
