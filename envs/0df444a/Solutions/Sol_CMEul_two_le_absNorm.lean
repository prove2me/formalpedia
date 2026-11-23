-- Prove2me | solution 1 for CMEul.two_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:51.988578+00:00
-- url     : https://prove2.me/submissions/22ace03d-81ce-4010-aeb6-40ed394e5eda

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorLocal

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
open CMEul
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
namespace CMEul
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : Ideal (𝓞 F)) (hv : v.IsMaximal) :
    2 ≤ Ideal.absNorm v := by
  have h1 : Ideal.absNorm v ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hv.ne_top
  have h0 : Ideal.absNorm v ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hv (RingOfIntegers.not_isField F)
  omega
end CMEul
