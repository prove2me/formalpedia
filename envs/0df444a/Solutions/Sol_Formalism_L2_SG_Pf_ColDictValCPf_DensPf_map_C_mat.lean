-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.DensPf.map_C_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:43:33.84445+00:00
-- url     : https://prove2.me/submissions/494fb5ce-29ab-4b9d-b2dd-cb7332588315

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
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
open Matrix MvPolynomial
open scoped ComplexOrder
open Formalism.L2.SG.Pf.ColDictValCPf.DensPf
variable {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf.DensPf
theorem _root_.solution (z : Bool × Fin n × Fin n → ℂ) (H : Matrix (Fin n) (Fin n) ℂ) :
    (eval z).mapMatrix (H.map C) = H := by
  ext i j; simp [RingHom.mapMatrix_apply]
end Formalism.L2.SG.Pf.ColDictValCPf.DensPf
