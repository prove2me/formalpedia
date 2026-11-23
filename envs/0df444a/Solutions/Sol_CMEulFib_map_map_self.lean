-- Prove2me | solution 1 for CMEulFib.map_map_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:47.424726+00:00
-- url     : https://prove2.me/submissions/a784886c-2b96-48e2-a937-46c0f131b6dc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_FibreShapeOf
import Theorems.Thm_CMEulFib_mem_map_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEulFib
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
namespace CMEulFib
theorem _root_.solution {B : Type*} [CommRing B] (σ : B ≃+* B) (hinv : ∀ x, σ (σ x) = x)
    (P : Ideal B) : (P.map σ).map σ = P := by
  ext y
  rw [mem_map_iff σ hinv, mem_map_iff σ hinv, hinv]
end CMEulFib
