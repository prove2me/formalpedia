-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.subst_pair_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:20:17.097667+00:00
-- url     : https://prove2.me/submissions/abdca540-7a73-4d37-8c47-3fd6a3542c9f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_hasSubst_pair
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
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
theorem _root_.solution {a b : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    {g : MvPowerSeries (Fin 2) R} (hg : MvPowerSeries.constantCoeff g = 0) (f : R⟦X⟧) :
    MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) (f.subst g)
      = f.subst (MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) g) := by
  have hg' : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const hg') (hasSubst_pair ha hb)]
end Formalism.L2.Th1.A.ZSer
