-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.bser_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:09.994791+00:00
-- url     : https://prove2.me/submissions/788ef00b-faa0-47c1-bcf3-281dbc91a1ce

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
theorem _root_.solution (b : ℤ_[p]) : constantCoeff (bser p K b) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, bser, coeff_mk, Ring.choose_zero_right, map_one]
end Formalism.ELL.PadicLogarithmSubstitution
