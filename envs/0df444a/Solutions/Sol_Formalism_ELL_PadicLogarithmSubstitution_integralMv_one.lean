-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.integralMv_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.900797+00:00
-- url     : https://prove2.me/submissions/f34845fa-d89e-4c24-99d7-cc574baa4d73

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicLogarithmSubstitution
theorem _root_.solution {σ : Type*} : IntegralMv (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp
end Formalism.ELL.PadicLogarithmSubstitution
