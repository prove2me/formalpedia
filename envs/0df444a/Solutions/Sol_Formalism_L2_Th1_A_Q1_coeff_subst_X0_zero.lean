-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q1.coeff_subst_X0_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:37:32.070911+00:00
-- url     : https://prove2.me/submissions/5554015a-8ecf-4cd4-92e4-e79c9ec70963

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Theorems.Thm_Formalism_L2_Th1_A_Q1_eq_single0
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_hasSubst2
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Q1
open CubeR
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.Q1
theorem _root_.solution (H : MvPowerSeries (Fin 2) R) (e : Fin 2 →₀ ℕ) (he : e 1 = 0) :
    MvPowerSeries.coeff e (H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0]) =
      MvPowerSeries.coeff e H := by
  classical
  have hs : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] :=
    hasSubst2 (by simp) (by simp)
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s n => (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] s) ^ n)
        = MvPowerSeries.X 0 ^ d 0 * 0 ^ d 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ e]
  · rw [hprod, he, pow_zero, mul_one, MvPowerSeries.coeff_X_pow]
    rw [if_pos (eq_single0 e he), smul_eq_mul, mul_one]
  · intro d hd
    rw [hprod]
    rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
    · rw [h1, pow_zero, mul_one, MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
      intro h
      apply hd
      rw [eq_single0 d h1]
      exact h.symm
    · rw [zero_pow h1.ne', mul_zero, map_zero, smul_zero]
end Formalism.L2.Th1.A.Q1
