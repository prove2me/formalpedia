-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.delSq_le_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:52.32014+00:00
-- url     : https://prove2.me/submissions/f7ffa91d-2141-4e37-9e9a-9b691be9a485

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_natW_anti_v
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleRowDividedPowerStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_highestWeightVectorMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (lam : DomWeight n) : delSq ℂ n lam ≤ dualWeyl ℂ n n lam.natW :=
  weylLeDual_of highestWeightVectorMem dualWeylModuleRowDividedPowerStable ℂ n n le_rfl _ (natW_anti_v lam)
end Formalism.L2.SG.Pf.ColDictValCPf
