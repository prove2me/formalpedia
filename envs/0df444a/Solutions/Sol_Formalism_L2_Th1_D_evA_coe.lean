-- Prove2me | solution 1 for Formalism.L2.Th1.D.evA_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:59.971785+00:00
-- url     : https://prove2.me/submissions/1a3eff3d-ff16-4e59-b144-35c953ac3a74

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.L2.Th1.D
theorem _root_.solution (k : ℕ) (r : MonoidAlgebra ℤ (muSub l)) : ((evA l k r : ringA l) : ℂ_[l]) = evK l k r := rfl
end Formalism.L2.Th1.D
