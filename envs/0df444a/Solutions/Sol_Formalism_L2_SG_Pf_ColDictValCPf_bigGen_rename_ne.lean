-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.bigGen_rename_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:42.380203+00:00
-- url     : https://prove2.me/submissions/9465124b-befc-4db5-a93f-96f54fbe6c8c

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
theorem _root_.solution (τ σ : ι) (h : σ ≠ τ) (a b : Fin n) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    bigGen τ a b (rename (Prod.mk σ) p) = Polynomial.C (rename (Prod.mk σ) p) := by
  have h' : (bigGen τ a b).comp (rename (Prod.mk σ)) = Polynomial.CAlgHom.comp (rename (R := ℂ) (Prod.mk σ)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [bigGen, h]
  have h2 := DFunLike.congr_fun h' p
  simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply] at h2
  exact h2
end Formalism.L2.SG.Pf.ColDictValCPf
