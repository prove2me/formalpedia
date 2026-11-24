-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordNormLpLemmas.lagCo_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:39:42.870967+00:00
-- url     : https://prove2.me/submissions/28d3c1dd-6ae1-4360-b514-9c6967082214

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialDegreeExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremCorollary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordNormLpLemmas
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas Formalism.FourierDecayAlt.P.RealWeightedForms
  Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.WordNormLpLemmas
theorem _root_.solution {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    F7.lagCo y j ≠ 0 := by
  unfold F7.lagCo
  refine Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.ne_of_mem_erase hi) (hy h).symm
end Formalism.FourierDecayAlt.P.WordNormLpLemmas
