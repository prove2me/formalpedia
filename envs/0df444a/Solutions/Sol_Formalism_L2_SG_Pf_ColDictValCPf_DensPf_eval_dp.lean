-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.DensPf.eval_dp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:29.3163+00:00
-- url     : https://prove2.me/submissions/22b5d60f-4ee2-4bb4-910a-658671f38ee3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry

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
open Matrix MvPolynomial
open scoped ComplexOrder
open Formalism.L2.SG.Pf.ColDictValCPf.DensPf
variable {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf.DensPf
theorem _root_.solution (G : Matrix (Fin n) (Fin n) ℂ) (z : Bool × Fin n × Fin n → ℂ) :
    eval z (dp G) = det (1 + (eval z).mapMatrix (Lp G)) := by
  rw [dp, RingHom.map_det, map_add, map_one]
end Formalism.L2.SG.Pf.ColDictValCPf.DensPf
