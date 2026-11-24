-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fock_pairing_divided_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:44.924878+00:00
-- url     : https://prove2.me/submissions/52e59ba6-b07a-4d34-a589-f335428b5fee

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_fockR_add_left
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_fockR_smul_left
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_fockR_add_right
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_fockR_smul_right
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_fockR_map
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_rowDiv_int
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_monomial_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_rowDiv_map


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
namespace Formalism.L2.G.Model.TS
theorem _root_.solution : FockRRowDivAdj := by
  intro R _ r n a b k f g
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    induction g using MvPolynomial.induction_on' with
    | monomial m' c' =>
      rw [adj_monomial_eq m c, adj_monomial_eq m' c', rowDiv_smul, rowDiv_smul,
        lclosedeq_rowDiv_map, lclosedeq_rowDiv_map]
      rw [adj_fockR_smul_left, adj_fockR_smul_right, adj_fockR_smul_left, adj_fockR_smul_right,
        adj_fockR_map, adj_fockR_map, adj_rowDiv_int]
    | add g1 g2 h1 h2 =>
      rw [rowDiv_add, adj_fockR_add_right, adj_fockR_add_right, h1, h2]
  | add f1 f2 h1 h2 =>
    rw [rowDiv_add, adj_fockR_add_left, adj_fockR_add_left, h1, h2]
end Formalism.L2.G.Model.TS
