-- Prove2me | solution 1 for Formalism.REAL.abs_compactHalfSum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:14.667816+00:00
-- url     : https://prove2.me/submissions/153ddcef-5791-4671-935d-fa1989749637

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ n := by
  unfold rhoC
  have c1 := Finset.card_filter_le (univ : Finset (Fin n)) (fun b => a < b ∧ ε b = ε a)
  have c2 := Finset.card_filter_le (univ : Finset (Fin n)) (fun b => b < a ∧ ε b = ε a)
  simp only [Finset.card_univ, Fintype.card_fin] at c1 c2
  have d1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by exact_mod_cast c1
  have d2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by exact_mod_cast c2
  have e1 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have e2 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith
end Formalism.REAL
