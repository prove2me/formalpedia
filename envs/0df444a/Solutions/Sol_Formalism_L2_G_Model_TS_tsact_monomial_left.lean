-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.tsact_monomial_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:08.092799+00:00
-- url     : https://prove2.me/submissions/1b352cbc-80a4-482e-ae5f-a34d2c5f7504

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_zero_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {σ R : Type*} [CommRing R]
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (m : σ →₀ ℕ) (a : R) (h : MvPolynomial σ R) :
    fockR (monomial m a) h = a * h.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp [tsact_zero_left]
  · unfold fockR
    rw [MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]
end Formalism.L2.G.Model.TS
