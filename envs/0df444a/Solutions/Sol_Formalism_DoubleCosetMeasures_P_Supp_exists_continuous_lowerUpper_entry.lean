-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.exists_continuous_lowerUpper_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:45.686091+00:00
-- url     : https://prove2.me/submissions/1e455f52-8373-4921-974f-e22c27f9f73d

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_lu_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
variable {K : Type} [CommRing K] {n : ℕ}
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P.Supp
theorem _root_.solution (m : ℕ) : ∃ E : Fin n → Fin n → Matrix (Fin n) (Fin n) K → K,
    (∀ i j, Continuous (E i j)) ∧ ∀ i j, (min i j).val < m → ∀ h u : Matrix (Fin n) (Fin n) K,
      IsLowUni h → IsUpUni u → E i j (h * u) = (h + u - 1) i j := by
  induction m with
  | zero => exact ⟨fun _ _ _ => 0, fun _ _ => continuous_const, fun i j h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨E, hEc, hE⟩ := ih
    refine ⟨fun i j => if (min i j).val < m then E i j else
      fun M => M i j - ∑ k, if k < i ∧ k < j then E i k M * E k j M else 0, ?_, ?_⟩
    · intro i j
      by_cases hm : (min i j).val < m
      · simp only [hm, if_true]; exact hEc i j
      · simp only [hm, if_false]
        refine (continuous_id.matrix_elem i j).sub (continuous_finsetSum _ fun k _ => ?_)
        by_cases hk : k < i ∧ k < j
        · simp only [hk, and_self, if_true]; exact (hEc i k).mul (hEc k j)
        · simp only [hk, if_false]; exact continuous_const
    · intro i j hij h u hh hu
      have hL : ∀ a b : Fin n, a < b → h a b = 0 := fun a b hab => hh.1 (OrderDual.toDual_lt_toDual.mpr hab)
      have hU : ∀ a b : Fin n, b < a → u a b = 0 := fun a b hab => hu.1 hab
      by_cases hm : (min i j).val < m
      · simp only [hm, if_true]; exact hE i j hm h u hh hu
      · simp only [hm, if_false]
        rw [lu_entry h u hh hu i j]
        have hs : ∀ k, (if k < i ∧ k < j then E i k (h * u) * E k j (h * u) else 0) =
            (if k < i ∧ k < j then h i k * u k j else 0) := by
          intro k
          by_cases hk : k < i ∧ k < j
          · have hkm : k.val < m := by
              have h1 : k < min i j := lt_min hk.1 hk.2
              have h2 : (k : ℕ) < (min i j : Fin n) := h1
              omega
            have hki : (min i k).val < m := by rw [min_eq_right hk.1.le]; exact hkm
            have hkj : (min k j).val < m := by rw [min_eq_left hk.2.le]; exact hkm
            rw [if_pos hk, if_pos hk, hE i k hki h u hh hu, hE k j hkj h u hh hu]
            rw [Matrix.sub_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply, hU i k hk.1,
              hL k j hk.2, Matrix.one_apply_ne hk.1.ne', Matrix.one_apply_ne hk.2.ne]
            ring
          · rw [if_neg hk, if_neg hk]
        rw [Finset.sum_congr rfl (fun k _ => hs k)]
        ring
end Formalism.DoubleCosetMeasures.P.Supp
