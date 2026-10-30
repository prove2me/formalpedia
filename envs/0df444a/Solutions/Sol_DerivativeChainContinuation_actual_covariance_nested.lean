-- Prove2me | solution 1 for DerivativeChainContinuation.actual_covariance_nested
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:35:40.143619+00:00
-- url     : https://prove2.me/submissions/c265db7a-ef7e-441d-b017-72ed4aaeae29

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_derivative_covariance_rescaling
import Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_nonneg
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hc : p.roots.sum = 0) :
    (((n+2 : ℝ)⁻¹ • rootCovariance p) -
      ((n+1 : ℝ)⁻¹ • rootCovariance (monicDerivative p))).PosSemidef := by
  rw [derivative_covariance_rescaling p hp n hdeg hc]
  apply Matrix.PosSemidef.one.smul
  exact div_nonneg (schoenbergDeficit_nonneg p hp (by omega) hc) (by positivity)
