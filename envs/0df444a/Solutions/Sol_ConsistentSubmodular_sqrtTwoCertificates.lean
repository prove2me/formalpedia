-- Prove2me | solution 1 for ConsistentSubmodular.sqrtTwoCertificates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:35.249793+00:00
-- url     : https://prove2.me/submissions/e62b714f-cb3e-4c24-be46-40b416634037

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate
import Theorems.Thm_ConsistentSubmodular_WindowInstance_halfMixture_certificate
import Theorems.Thm_ConsistentSubmodular_WindowInstance_exists_last_eligible

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- Theorem B.4 for one window and every admissible level. -/
theorem exists_halfMixtureCertificate {α β : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hαβ : α ≤ β) (hα : 2 * β * α ≤ 1) : Nonempty (W.Certificate α 3) := by
  obtain ⟨c, hDc, hafter⟩ := W.exists_last_eligible hβ'
  obtain ⟨Z, -⟩ := W.halfMixture_certificate hβ hβ' hαβ hα hDc hafter
  exact ⟨Z⟩

end WindowInstance

theorem one_div_sqrt_two_bounds :
    1 / 2 ≤ 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 ≤ 3 / 4 ∧
      2 * (1 / Real.sqrt 2) * (1 / Real.sqrt 2) ≤ 1 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by norm_num) hpos]
    nlinarith
  · rw [div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  · have he : 2 * (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 2 / (Real.sqrt 2 * Real.sqrt 2) := by
      field_simp
    rw [he, hs]
    norm_num

namespace Certificates

/-- Theorem 6: every window admits a `(1/√2, 3)`-certificate. This is
Theorem B.4 at `β = 1/√2`, where `α(β) = β = 1/(2β)`. -/
theorem sqrtTwoCertificates : SqrtTwoCertificatesGoal := by
  intro _ W
  obtain ⟨h1, h2, h3⟩ := one_div_sqrt_two_bounds
  exact W.exists_halfMixtureCertificate h1 h2 le_rfl h3

end Certificates

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : SqrtTwoCertificatesGoal :=
  Certificates.sqrtTwoCertificates

end
