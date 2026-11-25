-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.DensPf.map_Lp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:10.131951+00:00
-- url     : https://prove2.me/submissions/4b5d0042-23b0-423d-a8f3-0ccb33290947

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_map_C_mat
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
theorem _root_.solution (G : Matrix (Fin n) (Fin n) ℂ) (z : Bool × Fin n × Fin n → ℂ) :
    (eval z).mapMatrix (Lp G) =
      Matrix.of (fun i j => z (true, i, j) + Complex.I * z (false, i, j)) -
        G⁻¹ * Matrix.of (fun i j => z (true, j, i) - Complex.I * z (false, j, i)) * G := by
  have hP : (eval z).mapMatrix (Pm n) = Matrix.of (fun i j => z (true, i, j) + Complex.I * z (false, i, j)) := by
    ext i j; simp [Pm, RingHom.mapMatrix_apply]
  have hQ : (eval z).mapMatrix (Qm n) = Matrix.of (fun i j => z (true, j, i) - Complex.I * z (false, j, i)) := by
    ext i j; simp [Qm, RingHom.mapMatrix_apply]
  rw [Lp, map_sub, map_mul, map_mul, hP, hQ, map_C_mat, map_C_mat]
end Formalism.L2.SG.Pf.ColDictValCPf.DensPf
