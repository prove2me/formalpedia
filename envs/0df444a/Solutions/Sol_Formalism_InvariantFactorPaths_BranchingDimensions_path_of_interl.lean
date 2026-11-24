-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.path_of_interl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:51.856402+00:00
-- url     : https://prove2.me/submissions/55bf8da0-2f1c-45a6-9076-c4a9191b4525

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Ns_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_r_lt_k
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_add
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_be_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pre_size
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tails_range

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
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (hW : D.Wf) (hPre : D.IsPre mu)
    (hH : ∀ i', 1 ≤ i' → i' ≤ D.r → ∀ m, m < i' → ent mu (D.n0 + i') m = D.be)
    (hI : ∀ j, j < D.r → Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j))) :
    D.IsPATH mu := by
  have hNs := Ns_eq hW
  have hrk := r_lt_k hW
  have hk1 : 1 ≤ D.k := by omega
  have hD0 : Dom D.k (ent mu D.n0) := hPre.2.1 D.n0 le_rfl
  have hTR := tails_range hD0 hI
  have hn0be : ent mu D.n0 0 ≤ (D.be : ℤ) := by
    have h := (pre_size hk1 hPre D.n0 le_rfl).2
    have hb : (∑ l ∈ (Icc 1 D.n0).filter (fun l => D.vec l = true), D.B l) ≤ D.be := by
      rw [be_eq]
      unfold Letters.bePos
      omega
    exact h.trans (by exact_mod_cast hb)
  have hcur : ∀ j, j ≤ D.r → ∀ m, j ≤ m → ent mu (D.n0 + j) m = stage mu (D.n0 + j) (m - j) := by
    intro j _ m hm
    rw [stage_add, Nat.sub_add_cancel hm]
  have hDom : ∀ i, i ≤ D.Ns → Dom D.k (ent mu i) := by
    intro i hi
    by_cases hin : i ≤ D.n0
    · exact hPre.2.1 i hin
    obtain ⟨j, rfl⟩ : ∃ j, i = D.n0 + j := ⟨i - D.n0, by omega⟩
    have hjr : j ≤ D.r := by omega
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hIj := hI j' (by omega)
    intro m hm
    rcases lt_trichotomy (m + 1) (j' + 1) with h | h | h
    · rw [hH _ (by omega) hjr m (by omega), hH _ (by omega) hjr (m + 1) h]
    · have hm' : m = j' := by omega
      rw [hm', hH _ (by omega) hjr j' (by omega), hcur (j' + 1) hjr (j' + 1) le_rfl, Nat.sub_self]
      exact ((hTR (j' + 1) hjr 0 (by omega)).2).trans hn0be
    · rw [hcur _ hjr (m + 1) (by omega), hcur _ hjr m (by omega)]
      have hl : m + 1 - (j' + 1) = m - (j' + 1) + 1 := by omega
      rw [hl]
      exact (hIj (m - (j' + 1) + 1) (by omega)).1.trans (hIj (m - (j' + 1)) (by omega)).2
  refine ⟨hPre.1, hDom, ?_, ?_, hPre.2.2.2.2.1, hPre.2.2.2.2.2, hH⟩
  · intro i h1 hi hv
    by_cases hin : i ≤ D.n0
    · exact hPre.2.2.1 i h1 hin hv
    obtain ⟨j, rfl⟩ : ∃ j, i = D.n0 + j := ⟨i - D.n0, by omega⟩
    have hjr : j ≤ D.r := by omega
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hIj := hI j' (by omega)
    rw [show D.n0 + (j' + 1) - 1 = D.n0 + j' by omega]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rcases lt_trichotomy m j' with h | h | h
      · rw [hH j' (by omega) (by omega) m h, hH (j' + 1) (by omega) hjr m (by omega)]
      · rw [h, hH (j' + 1) (by omega) hjr j' (by omega), hcur j' (by omega) j' le_rfl, Nat.sub_self]
        exact ((hTR j' (by omega) 0 (by omega)).2).trans hn0be
      · rw [hcur j' (by omega) m (by omega), hcur (j' + 1) hjr m (by omega)]
        have hl : m - j' = m - (j' + 1) + 1 := by omega
        rw [hl]
        exact (hIj (m - (j' + 1)) (by omega)).2
    · by_cases h : m < j'
      · rw [hH (j' + 1) (by omega) hjr (m + 1) (by omega), hH j' (by omega) (by omega) m h]
      · rw [hcur (j' + 1) hjr (m + 1) (by omega), hcur j' (by omega) m (by omega)]
        have hl : m + 1 - (j' + 1) = m - j' := by omega
        rw [hl]
        exact (hIj (m - j') (by omega)).1
  · intro i h1 hi hv
    by_cases hin : i ≤ D.n0
    · exact hPre.2.2.2.1 i h1 hin hv
    · have h' := hW.2.2.2.2 i (by omega) hi
      simp [h'] at hv
end Formalism.InvariantFactorPaths.BranchingDimensions
