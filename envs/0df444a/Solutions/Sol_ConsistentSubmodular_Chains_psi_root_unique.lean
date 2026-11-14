-- Prove2me | solution 1 for ConsistentSubmodular.Chains.psi_root_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:08.190437+00:00
-- url     : https://prove2.me/submissions/b7264695-961f-40a2-a630-b393318bcac2

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

theorem hasDerivAt_psi (x : ℝ) :
    HasDerivAt psi (356 * x ^ 3 - 132 * x ^ 2 - 38 * x - 3) x := by
  have h := ((((hasDerivAt_pow 4 x).const_mul (89 : ℝ)).sub
    ((hasDerivAt_pow 3 x).const_mul (44 : ℝ))).sub
    ((hasDerivAt_pow 2 x).const_mul (19 : ℝ))).sub ((hasDerivAt_id x).const_mul (3 : ℝ))
  refine (h.add_const (1 : ℝ)).congr_deriv ?_
  norm_num
  ring

/-- `Ψ` is strictly convex on `[1/2, 1]`: `Ψ'' > 0` there, so `Ψ'` increases. -/
theorem psi_strictConvexOn : StrictConvexOn ℝ (Set.Icc (1 / 2) 1) psi := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _) continuous_psi.continuousOn
  rw [interior_Icc]
  intro a ha b hb hab
  rw [(hasDerivAt_psi a).deriv, (hasDerivAt_psi b).deriv]
  have hpos : 0 < 356 * (a ^ 2 + a * b + b ^ 2) - 132 * (a + b) - 38 := by
    nlinarith [ha.1, hb.1]
  have hkey : (356 * b ^ 3 - 132 * b ^ 2 - 38 * b - 3) - (356 * a ^ 3 - 132 * a ^ 2 - 38 * a - 3) =
      (b - a) * (356 * (a ^ 2 + a * b + b ^ 2) - 132 * (a + b) - 38) := by ring
  nlinarith [mul_pos (sub_pos.mpr hab) hpos]

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution {ξ₁ ξ₂ : ℝ} (h₁ : 1 / 2 < ξ₁) (h₁' : ξ₁ < 1) (h₂ : 1 / 2 < ξ₂)
    (h₂' : ξ₂ < 1) (hψ₁ : psi ξ₁ = 0) (hψ₂ : psi ξ₂ = 0) : ξ₁ = ξ₂ := by
  have key : ∀ {a b : ℝ}, 1 / 2 < a → a < b → b < 1 → psi a = 0 → psi b = 0 → False := by
    intro a b ha hab hb hψa hψb
    set lam := (b - a) / (b - 1 / 2) with hlam
    have hden : 0 < b - 1 / 2 := by linarith
    have hlam0 : 0 < lam := div_pos (by linarith) hden
    have hlam1 : 0 < 1 - lam := by
      rw [hlam, sub_pos, div_lt_one hden]
      linarith
    have hl : lam * (b - 1 / 2) = b - a := div_mul_cancel₀ _ hden.ne'
    have hcomb : lam • (1 / 2 : ℝ) + (1 - lam) • b = a := by
      simp only [smul_eq_mul]
      linear_combination (-1 : ℝ) * hl
    have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    have hb_mem : b ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by linarith, hb.le⟩
    have h := psi_strictConvexOn.2 hhalf_mem hb_mem (by linarith) hlam0 hlam1 (by ring)
    rw [hcomb, hψa, hψb] at h
    have hhalf : psi (1 / 2) = -83 / 16 := by norm_num [psi]
    simp only [smul_eq_mul, hhalf] at h
    nlinarith
  rcases lt_trichotomy ξ₁ ξ₂ with h | h | h
  · exact (key h₁ h h₂' hψ₁ hψ₂).elim
  · exact h
  · exact (key h₂ h h₁' hψ₂ hψ₁).elim

end
