-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.norm_phi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:12.494042+00:00
-- url     : https://prove2.me/submissions/b106ec76-808e-4b3a-b524-56dd80609de3

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
variable (p : ℕ) [Fact p.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
namespace Formalism.ELL.PadicLogarithmSubstitution
theorem _root_.solution (z : ℤ_[p]) : ‖phi p K z‖ ≤ 1 := by
  rw [phi, RingHom.comp_apply, norm_algebraMap']
  exact PadicInt.norm_le_one z
end Formalism.ELL.PadicLogarithmSubstitution
