-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.tsact_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:48.134867+00:00
-- url     : https://prove2.me/submissions/6aec576e-9159-43bf-8188-7fa1f3fe7679

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_eq_sum
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_fact_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {σ R : Type*} [CommRing R]
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (v : σ) (f h : MvPolynomial σ R) :
    fockR (f * X v) h = fockR f (pderiv v h) := by
  classical
  rw [tsact_eq_sum (f * X v) h _ (MvPolynomial.support_mul_X v f).le, Finset.sum_map]
  unfold fockR
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_pderiv, tsact_fact_succ]
  push_cast
  ring
end Formalism.L2.G.Model.TS
