-- Prove2me | solution 1 for CMEulFib.mem_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:21.280804+00:00
-- url     : https://prove2.me/submissions/25781a7b-3478-4018-9480-8cc0f65ecdca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_FibreShapeOf
import Theorems.Thm_CMEulFib_symm_eq

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
    (P : Ideal B) (y : B) : y ∈ P.map σ ↔ σ y ∈ P := by
  rw [← Ideal.symm_apply_mem_of_equiv_iff, symm_eq σ hinv]
end CMEulFib
