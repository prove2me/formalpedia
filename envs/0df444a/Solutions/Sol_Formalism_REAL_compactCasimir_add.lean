-- Prove2me | solution 1 for Formalism.REAL.compactCasimir_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:14.046462+00:00
-- url     : https://prove2.me/submissions/7dc92914-ccc3-4ba7-9baa-f8b18caae3df

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

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
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) (S P : Fin n → Fin n → Module.End ℂ W)
    (hc : ∀ a b c d, S a b * P c d = P c d * S a b) :
    CasK ε (fun a b => S a b + P a b) = CasK ε S + CasK ε P +
      2 * ∑ a, ∑ b, (if ε a = ε b then S a b * P b a else 0) := by
  simp only [CasK]
  have hswap : (∑ a, ∑ b, if ε a = ε b then P a b * S b a else 0) =
      ∑ a, ∑ b, if ε a = ε b then S a b * P b a else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : ε a = ε b
    · rw [if_pos h.symm, if_pos h, hc]
    · rw [if_neg (Ne.symm h), if_neg h]
  have expand : ∀ a b, (if ε a = ε b then (S a b + P a b) * (S b a + P b a) else 0) =
      (if ε a = ε b then S a b * S b a else 0) + (if ε a = ε b then P a b * P b a else 0) +
      ((if ε a = ε b then S a b * P b a else 0) + (if ε a = ε b then P a b * S b a else 0)) := by
    intro a b
    split_ifs
    · simp only [add_mul, mul_add]
      abel
    · simp
  simp only [expand, Finset.sum_add_distrib, hswap, two_mul]
end Formalism.REAL
