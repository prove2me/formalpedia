-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.choose_rec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.03836+00:00
-- url     : https://prove2.me/submissions/7791cbf3-431c-48c6-8f12-324c3c6a0d09

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
theorem _root_.solution (b : ℤ_[p]) (n : ℕ) :
    ((n + 1 : ℕ) : ℤ_[p]) * Ring.choose b (n + 1) = (b - n) * Ring.choose b n := by
  have h := Ring.choose_smul_choose b (Nat.le_succ n)
  rw [Nat.choose_succ_self_right, show n.succ - n = 1 by omega, Ring.choose_one_right,
    nsmul_eq_mul] at h
  rw [mul_comm (b - (n : ℤ_[p]))]
  exact h
end Formalism.ELL.PadicLogarithmSubstitution
