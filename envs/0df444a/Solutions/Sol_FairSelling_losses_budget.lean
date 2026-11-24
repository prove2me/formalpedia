-- Prove2me | solution 1 for FairSelling.losses_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:26.380427+00:00
-- url     : https://prove2.me/submissions/93201400-5873-4867-88d2-8653077b9721

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
import Theorems.Thm_FairSelling_eventCost_le
import Theorems.Thm_FairSelling_budget_ge_of_cover
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (hL : Losses v p T R D) {i : Fin n} (hi : i ∈ T) :
    ∃ E : EquiMMS (v i) p (MMS n (v i) p) n,
      ((T.card : ℝ)) * MMS n (v i) p ≤ E.budget R D := by
  classical
  obtain ⟨alloc, sold, paid, hempty, hdisj1, hdisj2, hdisjR, hcover, hpaid0, hmoney, htypes⟩ := hL
  obtain ⟨E, hE⟩ := htypes i hi
  refine ⟨E, ?_⟩
  have hμ0 : 0 ≤ MMS n (v i) p := MMS_nonneg hn (v i) p (hv i) hp
  have hbudget := budget_ge_of_cover E R D alloc sold paid hdisj2 hdisjR hcover hmoney
  -- every event costs at most `μ`, and the active agents carry no event
  have hcost_le : ∀ b, eventCost E (alloc b) (sold b) (paid b)
      ≤ if b ∈ T then 0 else MMS n (v i) p := by
    intro b
    by_cases hb : b ∈ T
    · obtain ⟨h1, h2, h3⟩ := hempty b hb
      rw [if_pos hb, h1, h2, h3]
      simp [eventCost, vbarSum]
    · rw [if_neg hb]
      exact eventCost_le E hp hμ0 (by rw [thr, rho]) (hdisj1 b) (hE b hb)
  have hsum_le : ∑ b, eventCost E (alloc b) (sold b) (paid b)
      ≤ ((n : ℝ) - T.card) * MMS n (v i) p := by
    refine le_trans (Finset.sum_le_sum (fun b _ => hcost_le b)) ?_
    have hkey : ∀ b : Fin n, (if b ∈ T then (0:ℝ) else MMS n (v i) p)
        = if b ∈ Finset.univ \ T then MMS n (v i) p else 0 := by
      intro b; by_cases hb : b ∈ T <;> simp [hb]
    have hcard : (((Finset.univ : Finset (Fin n)) \ T).card : ℝ) = (n : ℝ) - T.card := by
      have hle : T.card ≤ n := by simpa using Finset.card_le_univ T
      rw [Finset.card_univ_diff, Fintype.card_fin, Nat.cast_sub hle]
    calc ∑ b, (if b ∈ T then (0:ℝ) else MMS n (v i) p)
        = ∑ b, (if b ∈ Finset.univ \ T then MMS n (v i) p else 0) :=
          Finset.sum_congr rfl (fun b _ => hkey b)
      _ = ∑ _b ∈ (Finset.univ : Finset (Fin n)) \ T, MMS n (v i) p := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = (((Finset.univ : Finset (Fin n)) \ T).card : ℝ) * MMS n (v i) p := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) - T.card) * MMS n (v i) p := le_of_eq (by rw [hcard])
  have hexp : ((n : ℝ) - T.card) * MMS n (v i) p
      = (n : ℝ) * MMS n (v i) p - (T.card : ℝ) * MMS n (v i) p := by ring
  rw [hexp] at hsum_le
  linarith
end FairSelling
