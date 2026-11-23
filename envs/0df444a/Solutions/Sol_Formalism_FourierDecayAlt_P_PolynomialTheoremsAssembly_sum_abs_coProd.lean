-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.sum_abs_coProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:27.336622+00:00
-- url     : https://prove2.me/submissions/6dfc86da-c182-4af8-ae7a-72225b5741f3

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
theorem _root_.solution {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ j, |coProd grid j| = ∏ a, cg grid a := by
  simp only [coProd, Finset.abs_prod, cg]
  exact (Fintype.prod_sum (fun a i => |F7.lagCo (grid a) i|)).symm
end Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
