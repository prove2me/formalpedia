-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.frame_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:47.810747+00:00
-- url     : https://prove2.me/submissions/17ffb0f4-5462-44cb-9c71-479dfe5f86f3

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_extW_mk
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_extW_ge
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_extW_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_dom_le

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
namespace Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
theorem _root_.solution (hBr : BranchDim) (k n c : ℕ) (hk : k = n + (c + 1)) (be : ℤ) (x : Fin k → ℤ)
    (hd : Dom k (extW x)) (h0 : extW x 0 ≤ be) (hh : ∀ m, m < c → extW x m = be) :
    ∑ᶠ (y : Fin k → ℤ) (_ : Dom k (extW y) ∧ HStrip k (extW x) (extW y) ∧ ∀ m, m < c + 1 → extW y m = be),
      weylDim n (fun l => extW y (l + (c + 1))) = weylDim (n + 1) (fun l => extW x (l + c)) := by
  let mu : Fin (n + 1) → ℤ := fun l => extW x (l.val + c)
  have hmu : extW mu = fun l => extW x (l + c) := by
    funext l
    show extW (fun l : Fin (n + 1) => extW x (l.val + c)) l = _
    rw [extW_mk (fun l => extW x (l + c))]
    split_ifs with h
    · rfl
    · exact (extW_ge x (by omega)).symm
  have hdmu : Dom (n + 1) (extW mu) := by
    rw [hmu]; intro m hm
    have := hd (m + c) (by omega)
    have e : m + c + 1 = m + 1 + c := by omega
    rw [e] at this; exact this
  have hB := hBr n mu hdmu
  rw [hmu] at hB
  rw [← hB]
  let e : (Fin k → ℤ) → (Fin n → ℤ) := fun y l => extW y (l.val + (c + 1))
  have he : ∀ y, extW (e y) = fun l => extW y (l + (c + 1)) := by
    intro y; funext l
    show extW (fun l : Fin n => extW y (l.val + (c + 1))) l = _
    rw [extW_mk (fun l => extW y (l + (c + 1)))]
    split_ifs with h
    · rfl
    · exact (extW_ge y (by omega)).symm
  have hxbe : ∀ m, m < k → extW x m ≤ be := fun m hm => le_trans (dom_le hd m hm) h0
  refine finsum_mem_eq_of_bijOn e
    (s := {y | Dom k (extW y) ∧ HStrip k (extW x) (extW y) ∧ ∀ m, m < c + 1 → extW y m = be})
    (t := {la | Interl n (extW la) (fun l => extW x (l + c))}) ⟨?_, ?_, ?_⟩ ?_
  · rintro y ⟨_, hys, _⟩
    show Interl n (extW (e y)) _
    rw [he]
    intro l hl
    constructor
    · exact hys.2 (l + c) (by omega)
    · have := hys.1 (l + (c + 1)) (by omega)
      have e1 : l + 1 + c = l + (c + 1) := by omega
      show extW x (l + 1 + c) ≤ _
      rw [e1]; exact this
  · rintro y ⟨_, _, hyh⟩ y' ⟨_, _, hyh'⟩ heq
    refine extW_inj fun m hm => ?_
    by_cases hmc : m < c + 1
    · rw [hyh m hmc, hyh' m hmc]
    · have h1 := congrFun ((he y).symm.trans ((congrArg extW heq).trans (he y'))) (m - (c + 1))
      have e1 : m - (c + 1) + (c + 1) = m := by omega
      simp only [e1] at h1
      exact h1
  · intro la hla
    have hla' : ∀ l, l < n → extW la l ≤ extW x (l + c) ∧ extW x (l + 1 + c) ≤ extW la l := hla
    let y : Fin k → ℤ := fun m => if m.val < c + 1 then be else extW la (m.val - (c + 1))
    have hyd : ∀ m, extW y m = if m < k then (if m < c + 1 then be else extW la (m - (c + 1))) else 0 :=
      fun m => extW_mk (fun m => if m < c + 1 then be else extW la (m - (c + 1))) m
    have hy1 : ∀ m, m < c + 1 → extW y m = be := by
      intro m hm
      rw [hyd, if_pos (by omega), if_pos hm]
    have hy2 : ∀ l, extW y (l + (c + 1)) = extW la l := by
      intro l
      rw [hyd]
      by_cases hl : l < n
      · rw [if_pos (by omega), if_neg (by omega), Nat.add_sub_cancel]
      · rw [if_neg (by omega)]
        exact (extW_ge la (by omega)).symm
    refine ⟨y, ⟨?_, ⟨?_, ?_⟩, hy1⟩, ?_⟩
    · intro m hm
      by_cases hmc : m + 1 < c + 1
      · rw [hy1 _ hmc, hy1 m (by omega)]
      · obtain ⟨l, hl⟩ : ∃ l, m + 1 = l + (c + 1) := ⟨m - c, by omega⟩
        rw [hl, hy2]
        rcases Nat.eq_zero_or_pos l with h0l | h0l
        · rw [hy1 m (by omega)]
          exact le_trans (hla' l (by omega)).1 (hxbe _ (by omega))
        · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
          have e1 : m = l' + (c + 1) := by omega
          rw [e1, hy2]
          exact le_trans (hla' (l' + 1) (by omega)).1 (hla' l' (by omega)).2
    · intro m hm
      by_cases hmc : m < c + 1
      · rw [hy1 m hmc]; exact hxbe m hm
      · obtain ⟨l, rfl⟩ : ∃ l, m = l + (c + 1) := ⟨m - (c + 1), by omega⟩
        rw [hy2]
        have := (hla' l (by omega)).2
        have e1 : l + 1 + c = l + (c + 1) := by omega
        rw [e1] at this; exact this
    · intro m hm
      by_cases hmc : m + 1 < c + 1
      · rw [hy1 _ hmc, hh m (by omega)]
      · obtain ⟨l, hl⟩ : ∃ l, m = l + c := ⟨m - c, by omega⟩
        subst hl
        have e1 : l + c + 1 = l + (c + 1) := by omega
        rw [e1, hy2]
        exact (hla' l (by omega)).1
    · refine extW_inj fun m _ => ?_
      rw [he]
      exact hy2 m
  · intro y _
    rw [he]
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
