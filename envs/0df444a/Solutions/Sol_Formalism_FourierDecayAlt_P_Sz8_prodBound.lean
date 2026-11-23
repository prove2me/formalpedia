-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz8.prodBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:37.765497+00:00
-- url     : https://prove2.me/submissions/67d05e15-5e30-4a8f-82e5-47d92d17b73c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Sz8
namespace Formalism.FourierDecayAlt.P.Sz8
theorem _root_.solution {ι : Type} [Fintype ι] (F t : ι → ℝ) (K Ct : ℝ) (hK : 0 ≤ K)
    (hF : ∀ w, 0 ≤ F w ∧ F w ≤ K * t w) (ht : ∏ w, t w ≤ Ct) :
    ∏ w, F w ≤ Ct * K ^ Fintype.card ι := by
  have h1 : ∏ w, F w ≤ ∏ w, (K * t w) :=
    Finset.prod_le_prod (fun w _ => (hF w).1) (fun w _ => (hF w).2)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at h1
  have h2 : K ^ Fintype.card ι * ∏ w, t w ≤ K ^ Fintype.card ι * Ct :=
    mul_le_mul_of_nonneg_left ht (pow_nonneg hK _)
  linarith
end Formalism.FourierDecayAlt.P.Sz8
