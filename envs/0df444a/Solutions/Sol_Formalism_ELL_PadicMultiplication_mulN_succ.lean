-- Prove2me | solution 1 for Formalism.ELL.PadicMultiplication.mulN_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:45.934812+00:00
-- url     : https://prove2.me/submissions/4d513f3c-b2d6-468d-962c-4667f322788b

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.ELL Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {R : Type*} [CommRing R]
namespace Formalism.ELL.PadicMultiplication
theorem _root_.solution (F : FormalGroup R) (m : ℕ) :
    mulN F (m + 1) = MvPowerSeries.subst
      (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries := rfl
end Formalism.ELL.PadicMultiplication
