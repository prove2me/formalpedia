-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:10:00.625+00:00
-- url     : https://prove2.me/submissions/a408f542-f9bb-44cd-895c-f72c96856952

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_add_left
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_zero_left
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
theorem _root_.solution {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ t, f i) g = ∑ i ∈ t, fockR (f i) g := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fockR_zero_left]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add_left, ih]
end Formalism.L2.G.Model.TS
