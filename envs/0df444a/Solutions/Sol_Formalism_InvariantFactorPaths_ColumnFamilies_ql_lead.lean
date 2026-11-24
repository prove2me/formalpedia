-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:59:33.209862+00:00
-- url     : https://prove2.me/submissions/481082e6-a8d1-45fd-b1c6-15cd5c070688

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_be_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_strVert
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_range
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_le_lastIdx
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_P_unit
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_U
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_can


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    ∃ k0 : LamIdx n b, ql_be b k0 = nu - mu ∧
      (ql_ps b mu nu (canT mu, k0) (canT nu) = 1 ∨ ql_ps b mu nu (canT mu, k0) (canT nu) = -1) := by
  obtain ⟨hb, hnu, hs⟩ := ql_mem_strVert h
  have hN := ql_range hmu h
  set lo := mu (lastIdx n) with hlo
  set N := (nu 0 - lo).toNat with hNdef
  set k := ql_E lo N (qs_ext mu (canT mu)) with hk
  set i := ql_E lo N (qs_ext nu (canT nu)) with hi
  have hmk : ∀ (j : Fin N) a, a ∈ k j ↔ lo + 1 + (j : ℕ) ≤ mu a := fun j a => ql_mem_can hmu _ a
  have hmi : ∀ (j : Fin N) a, a ∈ i j ↔ lo + 1 + (j : ℕ) ≤ nu a := fun j a => ql_mem_can hnu _ a
  have hU : ∀ a, a ∈ ql_U N (fun j => i j \ k j) ↔ mu a < nu a := by
    intro a
    rw [ql_mem_U]
    simp only [mem_sdiff, hmk, hmi]
    constructor
    · rintro ⟨j, h1, h2⟩; omega
    · intro hlt
      have h1 : lo ≤ mu a := hmu (qb_le_lastIdx a)
      have h2 : nu a ≤ nu 0 := hnu (Fin.zero_le a)
      refine ⟨⟨(nu a - lo - 1).toNat, by omega⟩, ?_, ?_⟩
      · show lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ nu a; omega
      · show ¬ lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ mu a; omega
  have hind : ∀ a, (if a ∈ ql_U N (fun j => i j \ k j) then (1 : ℤ) else 0) = nu a - mu a := by
    intro a
    have := hb a
    split_ifs with h1
    · rw [hU] at h1; omega
    · rw [hU] at h1; omega
  have hcard : (ql_U N (fun j => i j \ k j)).card = b := by
    have : ((ql_U N (fun j => i j \ k j)).card : ℤ) = b := by
      rw [← hs, ← sum_congr rfl fun a _ => hind a, Finset.sum_boole, filter_mem_eq_inter, univ_inter]
    exact_mod_cast this
  refine ⟨⟨_, hcard⟩, ?_, ?_⟩
  · funext a
    rw [ql_be_apply, Pi.sub_apply]
    exact hind a
  · refine Int.isUnit_iff.1 (ql_P_unit k i ?_ ?_)
    · intro j a ha
      rw [hmk] at ha; rw [hmi]; exact ha.trans (hb a).1
    · intro j j' hjj
      rw [Finset.disjoint_left]
      intro a h1 h2
      simp only [mem_sdiff, hmk, hmi] at h1 h2
      have := hb a
      apply hjj; ext; omega
end Formalism.InvariantFactorPaths.ColumnFamilies
