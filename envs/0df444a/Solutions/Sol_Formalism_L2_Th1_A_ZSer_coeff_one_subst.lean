-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.coeff_one_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:52.051724+00:00
-- url     : https://prove2.me/submissions/45a0e849-bd3e-438e-a288-393d2f460b93

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.ZSer
local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.ZSer
theorem _root_.solution {f s : R⟦X⟧} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  have hs' := HasSubst.of_constantCoeff_zero hs
  obtain ⟨t, rfl⟩ : X ∣ s := X_dvd_iff.mpr hs
  erw [PowerSeries.coeff_subst hs', finsum_eq_single _ 1]
  · simp
  · intro d hd
    rcases d with _ | _ | d
    · simp
    · exact absurd rfl hd
    · rw [mul_pow]
      show coeff (d + 1 + 1) f • coeff 1 (X ^ (d + 1 + 1) * t ^ (d + 1 + 1)) = 0
      rw [coeff_X_pow_mul', if_neg (show ¬ (d + 1 + 1 ≤ 1) by omega), smul_zero]
end Formalism.L2.Th1.A.ZSer
