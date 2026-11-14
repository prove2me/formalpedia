-- Prove2me | solution 1 for ConsistentSubmodular.Chains.qStar_eq_uOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:52.558459+00:00
-- url     : https://prove2.me/submissions/2416a7cf-6f4d-4dcd-83c6-98f076ca46d0

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Constants
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique

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

theorem xiStar_lt_one : xiStar < 1 := xiStar_root.2.1

theorem quartic_eq_psi {t : ℝ} (ht : 0 < 1 + t) :
    quartic t = (1 + t) ^ 4 * psi (1 / (1 + t)) := by
  unfold quartic psi
  field_simp
  ring

theorem continuous_quartic : Continuous quartic := by
  unfold quartic
  fun_prop

theorem hasDerivAt_quartic (t : ℝ) :
    HasDerivAt quartic (4 * t ^ 3 + 3 * t ^ 2 - 44 * t - 87) t := by
  have h := ((((hasDerivAt_pow 4 t).add (hasDerivAt_pow 3 t)).sub
    ((hasDerivAt_pow 2 t).const_mul (22 : ℝ))).sub ((hasDerivAt_id t).const_mul (87 : ℝ)))
  refine (h.add_const (24 : ℝ)).congr_deriv ?_
  norm_num
  ring

/-- `Q' < 0` on `(0, 1)`, so `Q` is strictly decreasing on `[0, 1]`. -/
theorem quartic_strictAntiOn : StrictAntiOn quartic (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_quartic.continuousOn
  rw [interior_Icc]
  intro t ht
  rw [(hasDerivAt_quartic t).deriv]
  nlinarith [ht.1, ht.2, mul_pos ht.1 ht.1, mul_pos (mul_pos ht.1 ht.1) ht.1]

theorem xiStar_eq_qStar : xiStar = 1 / (1 + qStar) := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

theorem one_add_qStar : 1 + qStar = 1 / xiStar := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

/-- `Q(q) = 0`, since `Ψ(ξ⋆) = 0` and `ξ⋆ = 1/(1 + q)`. -/
theorem quartic_qStar : quartic qStar = 0 := by
  have hq : 0 < 1 + qStar := by
    rw [one_add_qStar]
    exact one_div_pos.mpr xiStar_pos
  rw [quartic_eq_psi hq, ← xiStar_eq_qStar, xiStar_root.2.2, mul_zero]

theorem qStar_pos : 0 < qStar := div_pos (by linarith [xiStar_lt_one]) xiStar_pos

theorem qStar_lt_one : qStar < 1 := by
  have h := xiStar_root.1
  unfold qStar
  rw [div_lt_one xiStar_pos]
  linarith

/-- The root of `Q` in `[0, 1]` is unique. -/
theorem eq_qStar {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) (hQ : quartic t = 0) : t = qStar :=
  quartic_strictAntiOn.injOn ⟨h₀, h₁⟩ ⟨qStar_pos.le, qStar_lt_one.le⟩ (hQ.trans quartic_qStar.symm)

/-- The identity `Q(2u² + 3u - 2) = Φ(u) (16u⁴ + 80u³ + 112u² + 60u + 59)` used in the
proof of Lemma 4. -/
theorem quartic_comp (u : ℝ) :
    quartic (2 * u ^ 2 + 3 * u - 2) =
      phi u * (16 * u ^ 4 + 80 * u ^ 3 + 112 * u ^ 2 + 60 * u + 59) := by
  unfold quartic phi
  ring

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution : qStar = uOne ^ 3 * (1 + uOne) := by
  have hu := uOne_bounds
  have hphi := phi_uOne
  have hlin : uOne ^ 3 * (1 + uOne) = 2 * uOne ^ 2 + 3 * uOne - 2 := by
    unfold phi at hphi
    linear_combination hphi
  have hQ : quartic (uOne ^ 3 * (1 + uOne)) = 0 := by
    rw [hlin, quartic_comp, phi_uOne, zero_mul]
  have h0 : 0 ≤ uOne ^ 3 * (1 + uOne) :=
    mul_nonneg (pow_nonneg uOne_pos.le 3) (by linarith [uOne_pos])
  have h1 : uOne ^ 3 * (1 + uOne) ≤ 1 := by
    have h3 : uOne ^ 3 ≤ (3 / 5) ^ 3 := pow_le_pow_left₀ uOne_pos.le hu.2.le 3
    nlinarith
  exact (eq_qStar h0 h1 hQ).symm

end
