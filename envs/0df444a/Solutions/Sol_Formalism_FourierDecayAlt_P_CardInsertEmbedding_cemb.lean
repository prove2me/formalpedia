-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CardInsertEmbedding.cemb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:09.112625+00:00
-- url     : https://prove2.me/submissions/e7c63241-02a6-4667-bfbd-c9e952894390

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_card_ins

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
theorem _root_.solution {m n k : ℕ} (b : Fin m) (hb : n < b.val) (h : (insert b (C2.iSet m n)).card = k) (t : Fin k) :
    (insert b (C2.iSet m n)).orderEmbOfFin h t = if ht : t.val < n then ⟨t.val, by omega⟩ else b := by
  have hk : k = n + 1 := by rw [← h, card_ins b hb (by omega)]
  subst hk
  have := Finset.orderEmbOfFin_unique h
    (f := fun t : Fin (n + 1) => if ht : t.val < n then (⟨t.val, by omega⟩ : Fin m) else b)
    (fun t => by
      beta_reduce
      split_ifs with ht
      · exact Finset.mem_insert_of_mem (by simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht)
      · exact Finset.mem_insert_self _ _)
    (fun x y hxy => by
      beta_reduce
      rw [Fin.lt_def] at hxy
      split_ifs with h1 h2 h2
      · rw [Fin.lt_def]; exact hxy
      · rw [Fin.lt_def]; simp only; omega
      · omega
      · omega)
  rw [← this]
end Formalism.FourierDecayAlt.P.CardInsertEmbedding
