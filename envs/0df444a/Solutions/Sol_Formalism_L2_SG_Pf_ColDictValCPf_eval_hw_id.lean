-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.eval_hw_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:52.46869+00:00
-- url     : https://prove2.me/submissions/357dc985-af25-4b5d-8f9f-debce4359ad4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Theorems.Thm_Formalism_GradedWeylDivisibility_eval_idPoint_lpMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (ν : Fin n → ℕ) : eval (idPoint ℂ n n) (hw ℂ (le_refl n) ν) = 1 := by
  simp only [hw, map_prod, map_pow, eval_idPoint_lpMinor, one_pow, Finset.prod_const_one]
end Formalism.L2.SG.Pf.ColDictValCPf
