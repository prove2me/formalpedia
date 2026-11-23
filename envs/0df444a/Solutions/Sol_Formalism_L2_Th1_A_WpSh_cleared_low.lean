-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.cleared_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:24.467347+00:00
-- url     : https://prove2.me/submissions/308aaabe-223e-4133-acd8-f47d2a3eed52

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_coeff_ofNat_mul
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_coeff_X_mul_derivative
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_derivative_X_sq_mul
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution [CharZero K] {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    coeff 0 r = 0 ∧ coeff 1 r = 0 ∧ coeff 2 r = g2 / 20 ∧ coeff 4 r = g3 / 28 := by
  have E := cleared_main h
  have lhs : ∀ n : ℕ, coeff n (4 * (X * derivative K r) + 12 * r) = (4 * (n : K) + 12) * coeff n r := by
    intro n
    rw [map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative]
    ring
  have r0 : coeff 0 r = 0 := by
    have e := congrArg (coeff 0) E
    rw [lhs, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at e
    have h12 : (4 * ((0 : ℕ) : K) + 12) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp e).resolve_left h12
  have r1 : coeff 1 r = 0 := by
    have e := congrArg (coeff 1) E
    rw [lhs, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 1))] at e
    have h16 : (4 * ((1 : ℕ) : K) + 12) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp e).resolve_left h16
  obtain ⟨t, rfl⟩ : X ^ 2 ∣ r := by
    rw [X_pow_dvd_iff]
    intro m hm
    interval_cases m <;> assumption
  have E2 : 4 * (X * derivative K t) + 20 * t = C g2 + X ^ 2 * (C g3 + X ^ 2 * (C g2 * t - 12 * t ^ 2
      - 4 * X ^ 4 * t ^ 3 + (2 * t + X * derivative K t) ^ 2)) := by
    have hX : (X : K⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [derivative_X_sq_mul] at E
    linear_combination E
  have lt : ∀ n : ℕ, coeff n (4 * (X * derivative K t) + 20 * t) = (4 * (n : K) + 20) * coeff n t := by
    intro n
    rw [map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative]
    ring
  have f0 := congrArg (coeff 0) E2
  rw [lt, map_add, coeff_C, if_pos rfl, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at f0
  have f2 := congrArg (coeff 2) E2
  rw [lt, map_add, coeff_C, if_neg (by norm_num : (2 : ℕ) ≠ 0), coeff_X_pow_mul', if_pos (le_refl 2),
    Nat.sub_self, map_add, coeff_C, if_pos rfl, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at f2
  push_cast at f0 f2
  refine ⟨r0, r1, ?_, ?_⟩
  · rw [coeff_X_pow_mul', if_pos (le_refl 2), Nat.sub_self, eq_div_iff (by norm_num)]
    linear_combination f0
  · rw [coeff_X_pow_mul', if_pos (by norm_num : 2 ≤ 4), show 4 - 2 = 2 from rfl, eq_div_iff (by norm_num)]
    linear_combination f2
end Formalism.L2.Th1.A.WpSh
