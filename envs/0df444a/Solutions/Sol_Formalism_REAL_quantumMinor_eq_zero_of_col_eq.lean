-- Prove2me | solution 1 for Formalism.REAL.quantumMinor_eq_zero_of_col_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:29.970006+00:00
-- url     : https://prove2.me/submissions/13104dc1-eec4-47ea-8b67-bfc34bc7308a

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_REAL_eq_zero_of_eq_neg_self_of_algebra_complex
import Theorems.Thm_Formalism_REAL_comp_swap_of_eq

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
theorem _root_.solution (hc : QSkewCol) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (a b : Fin t → Fin n) (u : ℂ) (p q : Fin t)
    (hpq : p ≠ q) (h : b p = b q) : qminor E a b u = 0 := by
  have h1 := hc A n t E hE a b (Equiv.swap p q) u
  rw [comp_swap_of_eq b p q h, Equiv.Perm.sign_swap hpq, Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one, neg_one_mul] at h1
  exact eq_zero_of_eq_neg_self_of_algebra_complex _ h1
end Formalism.REAL
