-- Prove2me | solution 1 for CMEulFib.comap_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:46.022803+00:00
-- url     : https://prove2.me/submissions/40eb802b-b490-4311-ae1c-0347a504b135

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
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B ≃+* B)
    (hinv : ∀ x, σ (σ x) = x) (hfix : ∀ y : A, σ (algebraMap A B y) = algebraMap A B y)
    (P : Ideal B) : (P.map σ).comap (algebraMap A B) = P.comap (algebraMap A B) := by
  ext y
  rw [Ideal.mem_comap, Ideal.mem_comap, mem_map_iff σ hinv, hfix]
end CMEulFib
