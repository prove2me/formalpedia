-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.U_mul_sin_node
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:01.789393+00:00
-- url     : https://prove2.me/submissions/8e013807-b100-4e88-b639-76737db292b3

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
theorem _root_.solution (m : ℕ) (j : ℕ) :
    (Chebyshev.U ℝ (m:ℤ)).eval (Chebyshev.node (m + 1) j) * Real.sin (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = 0 := by
  unfold Chebyshev.node
  rw [Chebyshev.U_real_cos]
  have : (((m:ℤ):ℝ) + 1) * (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = j * Real.pi := by
    push_cast; field_simp
  rw [this]
  exact Real.sin_nat_mul_pi j
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
