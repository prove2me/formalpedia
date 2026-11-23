-- Prove2me | solution 1 for DensInertW.iso_cntT_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:05.525747+00:00
-- url     : https://prove2.me/submissions/ca9893ba-4ca9-439c-a4f7-948faec0017a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_IsoPeel

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
    (W : Submodule L (Fin n → L)) :
    cntT q M W (0 : Matrix (Fin m) (Fin m) L) = (Finset.univ.filter (isoP (m := m) q M W)).card := by
  rw [cntT, ← Set.ncard_coe_finset]
  congr 1
  ext X
  simp [isoP]
end DensInertW
