-- Prove2me | solution 1 for Formalism.G0.countSubspacesEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:52.529804+00:00
-- url     : https://prove2.me/submissions/ee6b6f34-c25c-45ac-8cdf-0f7dea5640ec

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Theorems.Thm_Formalism_G0_SubspaceCountP_gb_eq_zero
import Theorems.Thm_Formalism_G0_SubspaceCountP_gb_mul_P
import Theorems.Thm_Formalism_G0_SubspaceCountP_card_LI_eq
import Theorems.Thm_Formalism_G0_SubspaceCountP_cast_prod_eq_P

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.G0
open SubspaceCountP
namespace Formalism.G0
theorem _root_.solution : SubspaceCount := by
  intro F W _ _ _ _ _ k
  classical
  have hcount : countBelow (⊤ : Submodule F W) k = Nat.card (Gr F W k) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by simp))
  rw [hcount]
  rcases lt_or_ge (finrank F W) k with hnk | hkn
  · rw [gb_eq_zero _ _ _ hnk, Nat.card_eq_zero]
    left
    constructor
    rintro ⟨U, hU⟩
    have := Submodule.finrank_le U
    omega
  · have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have h1 := card_LI_eq (F := F) (W := W) k
    rw [card_linearIndependent hkn] at h1
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, cast_prod_eq_P _ _ _ hq.le hkn, cast_prod_eq_P _ _ _ hq.le le_rfl] at h2
    have h3 := gb_mul_P (Fintype.card F : ℤ) (Fintype.card F) rfl (finrank F W) k
    have hP : P (Fintype.card F : ℤ) k k ≠ 0 := by
      unfold P
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have : (Fintype.card F : ℤ) ^ i < (Fintype.card F : ℤ) ^ k :=
        pow_lt_pow_right₀ (by exact_mod_cast hq) (Finset.mem_range.mp hi)
      omega
    have : (Nat.card (Gr F W k) : ℤ) = gaussBinom (Fintype.card F) (finrank F W) k :=
      mul_right_cancel₀ hP (h2.symm.trans h3.symm)
    exact_mod_cast this
end Formalism.G0
