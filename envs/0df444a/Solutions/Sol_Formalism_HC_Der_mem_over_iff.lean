-- Prove2me | solution 1 for Formalism.HC.Der.mem_over_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:22:06.851484+00:00
-- url     : https://prove2.me/submissions/723378b9-ca61-44de-bbb8-dceba65d2688

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsScalarTower ℚ E L]
omit [IsScalarTower ℚ E L] [NumberField E] [NumberField L]
namespace Formalism.HC.Der
theorem _root_.solution (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P] (x : 𝓞 E) :
    x ∈ P ↔ algebraMap (𝓞 E) (𝓞 L) x ∈ Q := by
  rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]
end Formalism.HC.Der
