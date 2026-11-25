-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.sl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:04.41734+00:00
-- url     : https://prove2.me/submissions/e8de5cce-a0ce-4b54-a070-148df211f86a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_sl_tenV
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
theorem _root_.solution (lam : ι → DomWeight n) (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ)
    {Q : MvPolynomial (ι × Fin n × Fin n) ℂ} (hQ : Q ∈ CSpanV lam) :
    sl τ₀ x Q ∈ delSq ℂ n (lam τ₀) := by
  simp only [CSpanV, delSq] at hQ ⊢
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    rw [sl_tenV, MvPolynomial.C_mul']
    exact Submodule.smul_mem _ _ (hf τ₀)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P R _ _ hP hR => rw [map_add]; exact Submodule.add_mem _ hP hR
  | smul c P _ hP => rw [map_smul]; exact Submodule.smul_mem _ c hP
end Formalism.L2.SG.Pf.ColDictValCPf
