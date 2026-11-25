-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.detBlocks_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:22.681945+00:00
-- url     : https://prove2.me/submissions/8bc8d27b-cb5c-4b27-b33e-340c44d98e0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_IsUnitDetOfUnitary
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_eval_detBlocks
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution : (detBlocks (ι := ι) (n := n)) ≠ 0 := by
  intro h
  have hx := eval_detBlocks (ι := ι) (n := n) (fun v => (1 : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)
  rw [h, map_zero] at hx
  have h1 : ∀ τ : ι, (Matrix.of fun a b : Fin n => (fun v : ι × Fin n × Fin n =>
      (1 : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2) (τ, a, b)) = 1 := fun τ => by
    ext a b
    simp
  simp [h1] at hx
end Formalism.L2.SG.Pf.ColDictValCPf
