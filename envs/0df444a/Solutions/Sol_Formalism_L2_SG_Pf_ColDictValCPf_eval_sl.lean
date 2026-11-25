-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.eval_sl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:29:44.53501+00:00
-- url     : https://prove2.me/submissions/dcc9ec26-b36d-4352-9b53-698ee943274e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
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
theorem _root_.solution (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) (y : Fin n × Fin n → ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval y (sl τ₀ x P) = eval (fun v => if v.1 = τ₀ then y v.2 else x v) P := by
  have h : (MvPolynomial.aeval y).comp (sl τ₀ x) =
      MvPolynomial.aeval (fun v => if v.1 = τ₀ then y v.2 else x v) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [sl, AlgHom.comp_apply, MvPolynomial.aeval_X]
    split_ifs <;> simp
  have h2 := DFunLike.congr_fun h P
  simp only [AlgHom.comp_apply] at h2
  exact h2
end Formalism.L2.SG.Pf.ColDictValCPf
