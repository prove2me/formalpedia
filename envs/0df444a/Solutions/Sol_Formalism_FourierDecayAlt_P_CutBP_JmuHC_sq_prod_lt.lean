-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.JmuHC.sq_prod_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:42.878947+00:00
-- url     : https://prove2.me/submissions/4e5f56b3-cce3-4304-a877-1c62d6bd75b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.JmuHC
open Finset
variable {n : ℕ}
namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC
theorem _root_.solution (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, g a b := by
  have h1 : ∀ a : Fin n, ∏ b ∈ univ.erase a, g a b =
      (∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) * ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b := by
    intro a
    rw [← prod_union]
    · congr 1
      ext b
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_filter, true_and]
      constructor
      · intro h; rcases lt_or_gt_of_ne h with h | h <;> [exact Or.inr h; exact Or.inl h]
      · rintro (h | h) <;> [exact ne_of_gt h; exact ne_of_lt h]
    · rw [disjoint_filter]
      intro b _ h1 h2
      exact lt_asymm h1 h2
  rw [prod_congr rfl (fun a _ => h1 a), prod_mul_distrib, sq]
  congr 1
  have hB : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b =
      ∏ b : Fin n, ∏ a ∈ univ.filter (fun a : Fin n => b < a), g a b :=
    prod_comm' (by intro a b; simp)
  rw [hB]
  exact prod_congr rfl fun b _ => prod_congr rfl fun a _ => hg b a
end Formalism.FourierDecayAlt.P.CutBP.JmuHC
