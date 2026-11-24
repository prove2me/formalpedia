-- Prove2me | solution 1 for Formalism.L2.Th1.F.LegendreModelEllipticTorsion.e2Summand_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:25:03.676202+00:00
-- url     : https://prove2.me/submissions/ca5753a1-6592-4604-b056-af58a0a10d8b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Legendre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F Formalism.L2.Th1.F.LegendreModelEllipticTorsion
namespace Formalism.L2.Th1.F.LegendreModelEllipticTorsion
theorem _root_.solution (z : ℍ) (a : ℕ) : e2Summand ((a : ℤ) + 1) z =
    -4 * π ^ 2 * ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((a + 1) * n : ℕ) := by
  have hw : 0 < (((a : ℂ) + 1) * (z : ℂ)).im := by
    have e : (((a : ℂ) + 1) * (z : ℂ)).im = ((a : ℝ) + 1) * (z : ℂ).im := by
      simp [Complex.mul_im]
    rw [e]
    exact mul_pos (by positivity) z.im_pos
  have H := EisensteinSeries.qExpansion_identity_pnat (k := 1) le_rfl ⟨((a : ℂ) + 1) * (z : ℂ), hw⟩
  have hc : ((⟨((a : ℂ) + 1) * (z : ℂ), hw⟩ : ℍ) : ℂ) = ((a : ℂ) + 1) * (z : ℂ) := rfl
  rw [hc] at H
  unfold EisensteinSeries.e2Summand
  have e1 : ∀ n : ℤ, eisSummand 2 ![(a : ℤ) + 1, n] z
      = 1 / (((a : ℂ) + 1) * (z : ℂ) + n) ^ (1 + 1) := by
    intro n
    simp [eisSummand, zpow_neg]
  have hq : ∀ n : ℕ+, cexp (2 * π * I * (((a : ℂ) + 1) * (z : ℂ))) ^ (n : ℕ)
      = cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ)) := by
    intro n
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [e1]
  rw [H]
  simp only [hq, pow_one]
  set S := ∑' n : ℕ+, ((n : ℕ) : ℂ) * cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ))
  simp only [Nat.factorial, Nat.cast_one, div_one, Nat.mul_one, Nat.succ_eq_add_one, zero_add]
  linear_combination (4 * (π : ℂ) ^ 2 * S) * Complex.I_sq
end Formalism.L2.Th1.F.LegendreModelEllipticTorsion
