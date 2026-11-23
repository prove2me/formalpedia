-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.lagCo_affine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:22.93236+00:00
-- url     : https://prove2.me/submissions/6d4ea364-334c-4896-bd02-42665ace7ea5

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
theorem _root_.solution {d : ℕ} (c h : ℝ) (x : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    lagCo (fun i => c + h * x i) j = (h⁻¹) ^ d * lagCo x j := by
  unfold lagCo
  have : ∀ i ∈ univ.erase j, ((c + h * x j) - (c + h * x i))⁻¹ = h⁻¹ * (x j - x i)⁻¹ := by
    intro i _
    rw [← mul_inv]; congr 1; ring
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ j)]
  simp
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
