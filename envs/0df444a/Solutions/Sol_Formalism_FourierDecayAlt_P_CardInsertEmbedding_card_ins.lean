-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CardInsertEmbedding.card_ins
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:13.054671+00:00
-- url     : https://prove2.me/submissions/9622fd34-66d7-4495-8d01-6c57a65124fc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_iSet_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.CardInsertEmbedding
open C2x2
namespace Formalism.FourierDecayAlt.P.CardInsertEmbedding
theorem _root_.solution {m n : ℕ} (b : Fin m) (hb : n < b.val) (hn : n ≤ m) :
    (insert b (C2.iSet m n)).card = n + 1 := by
  rw [Finset.card_insert_of_notMem, c2x3_iSet_card hn]
  simp [C2.iSet]; omega
end Formalism.FourierDecayAlt.P.CardInsertEmbedding
