-- Prove2me | solution 1 for FairSelling.MMS_liquid_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:07:33.431257+00:00
-- url     : https://prove2.me/submissions/4ddf7a40-5c5a-4efa-a4c1-a6f5c1cb7c0d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_MMSset_bddAbove_of
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {o : Outcome G n} (hval : o.Valid p) (hge : ∀ j, MMS n v p ≤ util v o j) (j : Fin n) :
    (∑ g ∈ o.kept j, p g) + o.money j ≤ MMS n v p := by
  classical
  set μ : ℝ := MMS n v p with hμ
  set P : ℝ := (∑ g ∈ o.kept j, p g) + o.money j with hP
  by_contra hcon
  push_neg at hcon
  have hμ0 : 0 ≤ μ := MMS_nonneg hn v p hv hp
  set eps : ℝ := (P - μ) / (2 * n) with heps
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have heps0 : 0 < eps := by
    rw [heps]
    apply div_pos (by linarith) (by linarith)
  -- the modified outcome: everything of part `j` is sold
  set o' : Outcome G n :=
    { sold := o.sold ∪ o.kept j
      kept := fun l => if l = j then ∅ else o.kept l
      money := fun l => if l = j then P - (n - 1 : ℝ) * eps else o.money l + eps } with ho'
  have hdisj_sj : Disjoint o.sold (o.kept j) := hval.1 j
  have hmoneyj : 0 ≤ P - (n - 1 : ℝ) * eps := by
    have h1 : (n - 1 : ℝ) * eps ≤ (n : ℝ) * eps := by nlinarith
    have h2 : (n : ℝ) * eps = (P - μ) / 2 := by
      rw [heps]; field_simp
    linarith
  have hsumsold : ∑ g ∈ o'.sold, p g = (∑ g ∈ o.sold, p g) + ∑ g ∈ o.kept j, p g := by
    simp only [ho']
    exact Finset.sum_union hdisj_sj
  have hsummoney : ∑ l, o'.money l = P + ∑ l ∈ Finset.univ.erase j, o.money l := by
    have hj : o'.money j = P - ((n:ℝ) - 1) * eps := by simp [ho']
    have hne : ∀ l ∈ Finset.univ.erase j, o'.money l = o.money l + eps := by
      intro l hl
      simp [ho', (Finset.mem_erase.mp hl).1]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj, Finset.sum_congr rfl hne,
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.erase j).card : ℝ) = (n : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub hn, Nat.cast_one]
    rw [hcard]
    ring
  have hvalid' : o'.Valid p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l
      by_cases hl : l = j
      · simp [ho', hl]
      · simp only [ho', if_neg hl]
        rw [Finset.disjoint_union_left]
        exact ⟨hval.1 l, hval.2.1 j l (fun h => hl h.symm)⟩
    · intro l l' hll
      simp only [ho']
      by_cases hl : l = j
      · simp [hl]
      · by_cases hl' : l' = j
        · simp [hl']
        · simp only [if_neg hl, if_neg hl']
          exact hval.2.1 l l' hll
    · intro l
      by_cases hl : l = j
      · simp only [ho', if_pos hl]; exact hmoneyj
      · simp only [ho', if_neg hl]
        have := hval.2.2.1 l
        linarith
    · rw [hsummoney, hsumsold, hP]
      have hms : ∑ l, o.money l ≤ ∑ g ∈ o.sold, p g := hval.2.2.2
      have hsplit : ∑ l, o.money l = o.money j + ∑ l ∈ Finset.univ.erase j, o.money l :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
      linarith
  -- every part of the modified outcome is worth more than `μ`
  have hbetter : ∀ l, μ + eps ≤ util v o' l := by
    intro l
    by_cases hl : l = j
    · subst hl
      have hgoal : util v o' l = P - ((n:ℝ) - 1) * eps := by simp [util, ho']
      rw [hgoal]
      have h1 : (n - 1 : ℝ) * eps ≤ (n : ℝ) * eps := by nlinarith
      have h2 : (n : ℝ) * eps = (P - μ) / 2 := by rw [heps]; field_simp
      have h3 : eps ≤ (P - μ) / 2 := by
        have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        nlinarith
      linarith
    · simp only [util, ho', if_neg hl]
      have := hge l
      simp only [util] at this
      linarith
  have hmem : μ + eps ∈ MMSset n v p := ⟨o', hvalid', hbetter⟩
  have hle : μ + eps ≤ MMS n v p := le_csSup (MMSset_bddAbove_of hn v p hv hp) hmem
  rw [← hμ] at hle
  linarith
end FairSelling
