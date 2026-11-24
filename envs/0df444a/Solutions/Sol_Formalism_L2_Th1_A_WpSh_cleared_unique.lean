-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.cleared_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:50.034567+00:00
-- url     : https://prove2.me/submissions/7b5b0f9d-2678-4536-b95d-012016292acc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_coeff_ofNat_mul
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_coeff_X_mul_derivative
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_coeff_shift_zero
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_main
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_main
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_ELL_Lemma2Aux_main
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution [CharZero K] {g2 g3 : K} {r s : K⟦X⟧} (hr : Cleared g2 g3 r)
    (hs : Cleared g2 g3 s) : r = s := by
  have hr' := cleared_main hr
  have hs' := cleared_main hs
  have key : ∀ n, coeff n (4 * (X * derivative K (r - s)) + 12 * (r - s)) =
      coeff n (X ^ 4 * ((r - s) * C g2) + X ^ 2 * ((r - s) * (-12 * (r + s)))
        + X ^ 4 * ((r - s) * (-4 * (r ^ 2 + r * s + s ^ 2)))
        + X ^ 3 * ((X * derivative K (r - s)) * (derivative K r + derivative K s))) := by
    intro n
    congr 1
    rw [map_sub]
    linear_combination hr' - hs'
  have main : ∀ n, (∀ k < n, coeff k (r - s) = 0) → coeff n (r - s) = 0 := by
    intro n hn
    have hn' : ∀ k < n, coeff k (X * derivative K (r - s)) = 0 := by
      intro k hk
      rw [coeff_X_mul_derivative, hn k hk, mul_zero]
    have t1 := coeff_shift_zero (m := 4) (C g2) hn (by norm_num)
    have t2 := coeff_shift_zero (m := 2) (-12 * (r + s)) hn (by norm_num)
    have t3 := coeff_shift_zero (m := 4) (-4 * (r ^ 2 + r * s + s ^ 2)) hn (by norm_num)
    have t4 := coeff_shift_zero (m := 3) (derivative K r + derivative K s) hn' (by norm_num)
    have e := key n
    simp only [map_add] at e
    rw [t1, t2, t3, t4, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative] at e
    have e2 : ((4 : K) * n + 12) * coeff n (r - s) = 0 := by linear_combination e
    have h4 : ((4 : K) * n + 12) ≠ 0 := by
      exact_mod_cast (show (4 * n + 12 : ℕ) ≠ 0 by omega)
    exact (mul_eq_zero.mp e2).resolve_left h4
  have all : ∀ n, coeff n (r - s) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih => exact main n ih
  rw [← sub_eq_zero]
  ext n
  rw [all n, map_zero]
end Formalism.L2.Th1.A.WpSh
