-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.special_independence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:09.067944+00:00
-- url     : https://prove2.me/submissions/1b3ea186-1e83-414d-8f0b-9a93c82e9c2a

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_special_det_monomial_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : SpecialIndep := by
  intro l hl J j hj
  have hM : (Matrix.of fun (i a : Fin J) =>
      (MvPolynomial.X a : MvPolynomial (Fin J) (ZMod l)) ^ (l ^ j i)) =
      Matrix.of fun r c => MvPolynomial.monomial (Finsupp.single c (l ^ j r)) (1 : ZMod l) := by
    ext r c; simp [MvPolynomial.X_pow_eq_monomial]
  rw [hM]
  refine special_det_monomial_ne_zero _ ?_
  intro p q h
  simp only at h
  ext c
  have hc := DFunLike.congr_fun h c
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc
  exact congrArg _ (hj (Nat.pow_right_injective hl.out.two_le hc))
end Formalism.DworkPowerSeriesWeights
