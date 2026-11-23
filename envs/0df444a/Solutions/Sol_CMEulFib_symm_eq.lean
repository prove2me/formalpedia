-- Prove2me | solution 1 for CMEulFib.symm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:52.253856+00:00
-- url     : https://prove2.me/submissions/81923812-162b-473f-9126-4a9cc4ae3249

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_FibreShapeOf

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
theorem _root_.solution {B : Type*} [CommRing B] (σ : B ≃+* B) (hinv : ∀ x, σ (σ x) = x) (x : B) :
    σ.symm x = σ x :=
  σ.symm_apply_eq.mpr (hinv x).symm
end CMEulFib
