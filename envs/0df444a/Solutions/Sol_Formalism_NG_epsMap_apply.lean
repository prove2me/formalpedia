-- Prove2me | solution 1 for Formalism.NG.epsMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:50.742798+00:00
-- url     : https://prove2.me/submissions/428e2478-8fd5-4a19-90e4-496316d6bf5f

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.NG
universe u
variable {O OO : Type*} [CommRing O] [Ring OO] [Algebra O OO]
namespace Formalism.NG
theorem _root_.solution {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A]
    [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) (x : epsImg O (M := A) ε) :
    ((epsMap (O := O) φ ε x : epsImg O (M := B) ε) : B) = φ x := rfl
end Formalism.NG
