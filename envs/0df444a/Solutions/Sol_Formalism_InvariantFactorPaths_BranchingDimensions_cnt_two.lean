-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.cnt_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:39.560581+00:00
-- url     : https://prove2.me/submissions/375f5a44-7f30-43d5-9a73-7b45eece3fc3

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementL
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LDigits
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_shift_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_cnt_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_cnt_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
section Digits
variable {I1 I2 : Type}
end Digits
section Residue
private theorem eq_of_add_pred_mul_mod_eq_of_lt (Q c a b : ℕ) (hQ : 1 ≤ Q) (ha : a < Q) (hb : b < Q)
    (h : (c + (Q - 1) * a) % Q = (c + (Q - 1) * b) % Q) : a = b := by
  have h1 : (a + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q a _ c hQ).2 (Nat.mod_mod _ _)
  have h2 : (b + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q b _ c hQ).2 (by rw [Nat.mod_mod, h])
  have h3 : Nat.ModEq Q (a + (c + (Q - 1) * a) % Q) (b + (c + (Q - 1) * a) % Q) :=
    h1.trans h2.symm
  have h4 : Nat.ModEq Q a b := Nat.ModEq.add_right_cancel' _ h3
  have h5 : a % Q = b % Q := h4
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h5
end Residue
section Exact
end Exact
end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (T Q c : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) : T - (Q - T) ≤ cnt T Q 2 c := by
  have h2 : cnt T Q 2 c = ∑ a : Fin T, cnt T Q 1 (c + (Q - 1) * a) :=
    cnt_succ T Q 1 c hQ
  rw [h2]
  simp only [cnt_one T Q _ hT]
  have hsplit : (∑ a : Fin T, if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
      ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card = T := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have hone : ∀ a : Fin T, ((if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
        (if ¬ (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) : ℕ) = 1 := by
      intro a
      by_cases h : (c + (Q - 1) * (a : ℕ)) % Q < T <;> simp [h]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hle : ((Finset.univ : Finset (Fin T)).filter
      (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ Q - T := by
    have hc : ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ (Finset.Ico T Q).card := by
      apply Finset.card_le_card_of_injOn (fun a : Fin T => (c + (Q - 1) * (a : ℕ)) % Q)
      · intro a ha
        have ha' : T ≤ (c + (Q - 1) * (a : ℕ)) % Q := by simpa using ha
        simp only [Finset.mem_coe, Finset.mem_Ico]
        exact ⟨ha', Nat.mod_lt _ (by omega)⟩
      · intro a _ b _ hab
        exact Fin.ext (eq_of_add_pred_mul_mod_eq_of_lt Q c a b hQ (lt_of_lt_of_le a.isLt hT)
          (lt_of_lt_of_le b.isLt hT) hab)
    rw [Nat.card_Ico] at hc
    exact hc
  omega
end Formalism.InvariantFactorPaths.BranchingDimensions
