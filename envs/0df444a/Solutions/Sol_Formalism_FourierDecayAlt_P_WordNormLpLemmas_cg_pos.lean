-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordNormLpLemmas.cg_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:04:31.318963+00:00
-- url     : https://prove2.me/submissions/06bddcf3-51ab-4d0d-b03f-f35f7de65053

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialDegreeExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremCorollary
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordNormLpLemmas_lagCo_ne

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
theorem _root_.solution {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) : 0 < cg y := by
  unfold cg
  have h0 : 0 < |F7.lagCo y 0| := abs_pos.mpr (lagCo_ne y hy 0)
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun k => |F7.lagCo y k|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ 0))
end Formalism.FourierDecayAlt.P.WordNormLpLemmas
