-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.tsact_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:02.439716+00:00
-- url     : https://prove2.me/submissions/e22fe866-dcc4-45cf-85c0-0e1395a53711

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_eq_sum

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
theorem _root_.solution (c : R) (f g : MvPolynomial σ R) :
    fockR (c • f) g = c * fockR f g := by
  rw [tsact_eq_sum (c • f) g f.support MvPolynomial.support_smul]
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring
end Formalism.L2.G.Model.TS
