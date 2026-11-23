-- Prove2me | solution 1 for Formalism.ELL.PadicMultiplication.integral_natMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.951075+00:00
-- url     : https://prove2.me/submissions/4e1808fb-e12a-4754-9901-a143f52591ce

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicMultiplication
theorem _root_.solution (F : FormalGroup (unitBall K)) (m n : ℕ) :
    ‖coeff n ((mulN F m).map (unitBall K).subtype)‖ ≤ 1 := by
  rw [PowerSeries.coeff_map]
  exact (coeff n (mulN F m)).2
end Formalism.ELL.PadicMultiplication
