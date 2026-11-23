-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.lagCo_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:48.739251+00:00
-- url     : https://prove2.me/submissions/bccf745d-0abf-4e6b-a367-2f19f170536a

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    Formalism.FourierDecayAlt.F7.lagCo y j ≠ 0 := by
  unfold Formalism.FourierDecayAlt.F7.lagCo
  exact Finset.prod_ne_zero_iff.mpr fun i hi =>
    inv_ne_zero (sub_ne_zero.mpr (hy.ne (Finset.ne_of_mem_erase hi).symm))
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses
