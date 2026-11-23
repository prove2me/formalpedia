-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.integral_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:05.54459+00:00
-- url     : https://prove2.me/submissions/2b5cac9e-bdee-4e8b-94cc-52938b1b04ed

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
variable [IsUltrametricDist K]
namespace Formalism.ELL.EulerSeries
theorem _root_.solution (F : MvPowerSeries σ (unitBall K)) :
    IntegralMv (MvPowerSeries.map (unitBall K).subtype F) := fun d => by
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff d F).2
end Formalism.ELL.EulerSeries
