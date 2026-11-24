-- Prove2me | solution 1 for Formalism.NG.IdempotentImageSmul.eps_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:38.853516+00:00
-- url     : https://prove2.me/submissions/22dcb3f3-76e4-496a-a400-7471659d2c9d

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentImageSmul
variable {O OO M Q : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M] [Module OO M]
    [Module O M] [IsScalarTower O OO M] [AddCommGroup Q] [Module O Q] (ε : OO)
variable {ε}
namespace Formalism.NG.IdempotentImageSmul
theorem _root_.solution (hε : IsIdempotentElem ε) (x : epsIdeal O ε) : ε * x.1 = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  simp only [LinearMap.mulLeft_apply] at hy
  rw [← hy, ← mul_assoc, hε.eq]
end Formalism.NG.IdempotentImageSmul
