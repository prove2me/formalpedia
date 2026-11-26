-- Prove2me | solution 1 for FirstPassageLinearTransport.centralOrbitScale_eq_rho_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:24.772213+00:00
-- url     : https://prove2.me/submissions/8b87ce3e-e865-4029-847d-17998ca2331b

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (k : ℕ) :
    centralOrbitScale k = rho ^ k := by
  unfold centralOrbitScale rho
  rw [Real.rpow_div_two_eq_sqrt (k : ℝ) (by norm_num),
    Real.rpow_natCast, div_pow]
end FirstPassageLinearTransport
