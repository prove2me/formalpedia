-- Prove2me | solution 1 for DensInertW.an_cntT_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:17.409702+00:00
-- url     : https://prove2.me/submissions/8f69703b-751b-4818-a7d0-5b59735b11a6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
open DensInertW.Sub
variable {L : Type} [Field L]
open Classical
namespace DensInertW
theorem _root_.solution [Fintype L] {n m q : ℕ} (M : Matrix (Fin n) (Fin n) L)
    (W : Submodule L (Fin n → L)) (B : Matrix (Fin m) (Fin m) L) :
    cntT q M W B = (Finset.univ.filter (anP q M W B)).card := by
  unfold cntT
  rw [← Set.ncard_coe_finset]
  congr 1
  ext X
  simp [anP]
end DensInertW
