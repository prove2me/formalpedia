-- Prove2me | solution 1 for Formalism.REAL.rho_rhoN_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:33.122801+00:00
-- url     : https://prove2.me/submissions/46e27b50-6733-4c55-854a-67ba43288e64

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Theorems.Thm_Formalism_REAL_rho_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  unfold rhoN
  have h1 := rho_card_le (fun b => a < b ∧ ε b ≠ ε a)
  have h2 := rho_card_le (fun b => b < a ∧ ε b ≠ ε a)
  have h3 := Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card
  have h4 := Nat.cast_nonneg (α := ℝ) (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card
  constructor <;> linarith
end Formalism.REAL
