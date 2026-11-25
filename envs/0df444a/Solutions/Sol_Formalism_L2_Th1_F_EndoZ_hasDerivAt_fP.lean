-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.hasDerivAt_fP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:50.027971+00:00
-- url     : https://prove2.me/submissions/87db507f-2371-4912-b39d-f34e7392ff98

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_sub
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_wp_eq
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_wp_logDeriv
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_ne_zero_of_notMem
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wp_eq
import Theorems.Thm_Formalism_L2_Th1_F_PDeriv_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
theorem _root_.solution (L : PeriodPair) {P w : ℂ} (hP : P ∉ L.lattice) (hw : w ∈ U L P) :
    HasDerivAt (fP L P) (fP L P w * mP L P w) w := by
  obtain ⟨hw0, hwp, hwm⟩ := hw
  have hne : w ≠ 0 := ne_zero_of_notMem L hw0
  have hex : L.weierstrassPExcept 0 = fun u => L.weierstrassP u - (u ^ 2)⁻¹ := by
    funext u; rw [wp_eq L u]; ring
  have hinv : HasDerivAt (fun u : ℂ => (u ^ 2)⁻¹) (-(2 * w) / (w ^ 2) ^ 2) w :=
    ((hasDerivAt_pow 2 w).inv (pow_ne_zero 2 hne)).congr_deriv (by norm_num <;> ring)
  have hE : HasDerivAt (L.weierstrassPExcept 0)
      (L.derivWeierstrassP w - (-(2 * w) / (w ^ 2) ^ 2)) w := by
    rw [hex]; exact (PDeriv.hasDerivAt_P L hw0).sub hinv
  have hF : HasDerivAt (fP L P) (2 * w * (L.weierstrassPExcept 0 w - L.weierstrassP P)
      + w ^ 2 * (L.derivWeierstrassP w - (-(2 * w) / (w ^ 2) ^ 2))) w := by
    have h1 := ((hasDerivAt_pow 2 w).mul (hE.sub_const (L.weierstrassP P))).const_add 1
    exact h1.congr_deriv (by norm_num <;> ring)
  refine hF.congr_deriv ?_
  rw [wp_logDeriv L hP hw0 hwp hwm]
  simp only [fP, mP, hex]
  field_simp
  ring
end Formalism.L2.Th1.F.EndoZ
