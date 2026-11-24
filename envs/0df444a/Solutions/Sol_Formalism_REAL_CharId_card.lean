-- Prove2me | solution 1 for Formalism.REAL.CharId_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:44.150941+00:00
-- url     : https://prove2.me/submissions/64d70260-d8e4-40e4-b7e2-8b5c6905a0c6

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (t : Fin n) :
    (((univ.filter (fun a : Fin n => t < a)).card : ℕ) : ℂ) = (n : ℂ) - 1 - ((t : ℕ) : ℂ) := by
  have ht := t.isLt
  have hI : univ.filter (fun a : Fin n => t < a) = Finset.Ioi t := by
    ext a
    simp
  have h : (univ.filter (fun a : Fin n => t < a)).card = n - 1 - t := by
    rw [hI, Fin.card_Ioi]
  rw [h, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp
end Formalism.REAL
