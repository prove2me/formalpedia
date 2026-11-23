-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.det_sum_mul_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:29.803955+00:00
-- url     : https://prove2.me/submissions/30756d92-bfcf-41a0-b729-06af8e68d9c9

import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership

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
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {S : Type*} [CommRing S] {p n : ℕ} (u : Fin p → Fin n → S)
    (y : Fin n → Fin p → S) :
    (Matrix.of fun (r r' : Fin p) => ∑ a, u r a * y a r').det =
      ∑ A : Fin p → Fin n, (∏ r', y (A r') r') *
        (Matrix.of fun (r r' : Fin p) => u r (A r')).det := by
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun σ _ => ?_
  ring
end Formalism.DworkPowerSeriesWeights
