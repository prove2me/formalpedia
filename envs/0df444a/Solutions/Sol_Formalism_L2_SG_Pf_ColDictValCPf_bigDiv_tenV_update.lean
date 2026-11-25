-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.bigDiv_tenV_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:09.283646+00:00
-- url     : https://prove2.me/submissions/98739422-5730-4a42-b70c-735f8e9045ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tenV_update
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_bigGen_rename_self
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_bigGen_rename_ne
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
theorem _root_.solution (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ : ι) (a b : Fin n) (k : ℕ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) :
    bigDiv τ a b k (tenV (Function.update f τ p)) =
      tenV (Function.update f τ (rowDiv ℂ a b k p)) := by
  simp only [bigDiv, rowDiv]
  rw [tenV_update, tenV_update, map_mul, map_prod, bigGen_rename_self,
    Finset.prod_congr rfl (fun σ hσ => bigGen_rename_ne τ σ (Finset.ne_of_mem_erase hσ) a b (f σ)),
    ← map_prod Polynomial.C, Polynomial.coeff_mul_C, Polynomial.coeff_map]
  rfl
end Formalism.L2.SG.Pf.ColDictValCPf
