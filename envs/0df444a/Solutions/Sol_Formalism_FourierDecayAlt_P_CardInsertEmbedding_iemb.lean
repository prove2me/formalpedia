-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CardInsertEmbedding.iemb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:14.282697+00:00
-- url     : https://prove2.me/submissions/126445a0-371f-4f7a-ae5f-fec2b79c897e

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
theorem _root_.solution {m n k : ℕ} (hn : n ≤ m) (h : (C2.iSet m n).card = k) (t : Fin k) :
    ((C2.iSet m n).orderEmbOfFin h t).val = t.val := by
  have hk : k = n := by rw [← h, c2x3_iSet_card hn]
  subst hk
  have := Finset.orderEmbOfFin_unique h (f := fun t : Fin k => (⟨t.val, by omega⟩ : Fin m))
    (fun t => by simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact t.isLt)
    (fun x y hxy => hxy)
  rw [← this]
end Formalism.FourierDecayAlt.P.CardInsertEmbedding
