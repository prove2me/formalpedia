-- Prove2me | solution 1 for Formalism.L2.Th1.F.cm_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:15.465798+00:00
-- url     : https://prove2.me/submissions/4f42430a-447f-4318-a487-8a219db3c57f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_theta_sq
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_coord
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Cm1
namespace Formalism.L2.Th1.F
theorem _root_.solution : CmOrder := by
  intro a b c d ha hd h hg α hα
  have hsq := Formalism.L2.Th1.F.Cm1.theta_sq a b c d h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have haL : (a : ℂ) ∈ (cmPair a b d ha hd).lattice :=
    (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mpr ⟨1, 0, by simp⟩
  have hωL : cmTheta b d ∈ (cmPair a b d ha hd).lattice :=
    (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mpr ⟨0, 1, by simp⟩
  obtain ⟨x, y, eq1⟩ := (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mp (hα _ haL)
  obtain ⟨u, v, eq2⟩ := (Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd _).mp (hα _ hωL)
  obtain ⟨k1, k2⟩ := Formalism.L2.Th1.F.Cm1.coord a b d ha hd ((u * a + y * c : ℤ) : ℝ)
    ((v * a - x * a - y * b : ℤ) : ℝ)
    (by push_cast; linear_combination (a : ℂ) * eq2 - cmTheta b d * eq1 + (y : ℂ) * hsq)
  have e1 : u * (a : ℤ) + y * c = 0 := by exact_mod_cast k1
  have e2 : v * (a : ℤ) - x * a - y * b = 0 := by exact_mod_cast k2
  have hb : y * b = a * (v - x) := by linear_combination -e2
  have hc : y * c = -(a * u) := by linear_combination e1
  obtain ⟨A, B, g1⟩ : ∃ A B : ℤ, ((Int.gcd (a : ℤ) b : ℕ) : ℤ) * A + c * B = 1 :=
    ⟨Int.gcdA ((Int.gcd (a : ℤ) b : ℕ) : ℤ) c, Int.gcdB ((Int.gcd (a : ℤ) b : ℕ) : ℤ) c, by
      rw [← Int.gcd_eq_gcd_ab, hg, Nat.cast_one]⟩
  obtain ⟨A', B', g2⟩ : ∃ A B : ℤ, (a : ℤ) * A + b * B = ((Int.gcd (a : ℤ) b : ℕ) : ℤ) :=
    ⟨_, _, (Int.gcd_eq_gcd_ab _ _).symm⟩
  have hy : y = a * (y * A' * A + (v - x) * B' * A - u * B) := by
    linear_combination -y * g1 - y * A * g2 + B' * A * hb + B * hc
  refine ⟨x, y * A' * A + (v - x) * B' * A - u * B, ?_⟩
  have hyC : (y : ℂ) = (a : ℂ) * ((y * A' * A + (v - x) * B' * A - u * B : ℤ) : ℂ) := by
    exact_mod_cast hy
  apply mul_right_cancel₀ ha0
  linear_combination -eq1 + cmTheta b d * hyC
end Formalism.L2.Th1.F
