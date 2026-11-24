-- Prove2me | solution 1 for Formalism.NG.IdempotentImageSmul.eps_smul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:39.731194+00:00
-- url     : https://prove2.me/submissions/b2c7dfec-d9ba-489b-a714-d23c6c85855b

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
theorem _root_.solution (hε : IsIdempotentElem ε) (y : epsImg O (M := M) ε) : ε • y.1 = y.1 := by
  obtain ⟨z, hz⟩ := y.2
  rw [← hz]
  show ε • ε • z = ε • z
  rw [← mul_smul, hε.eq]
end Formalism.NG.IdempotentImageSmul
