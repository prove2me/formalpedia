-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.no_better_than_one_over_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:55:12.492751+00:00
-- url     : https://prove2.me/submissions/05b32e12-cb9d-4ec0-8e26-5b31a0fcef6f

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_exists_kept_subset
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_price_sum
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_val_zero
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_val_ne_zero
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_MMSEP_agent_zero
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_MMSEP_agent_other

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleFour
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ o : Outcome (Fin (N + 2)) (N + 2),
      o.Valid (price N) → o.EqualProceeds (price N) →
      ∃ i, util (val N L i) o i
            < (1 / ((N : ℝ) + 2) + ε) * MMSEP (N + 2) (val N L i) (price N) := by
  refine ⟨((N : ℝ) + 2) / ε + 1, by nlinarith [div_pos (show (0:ℝ) < (N:ℝ) + 2 by positivity) hε],
    ?_⟩
  set L : ℝ := ((N : ℝ) + 2) / ε + 1 with hLdef
  have hNpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hL1 : 1 ≤ L := by
    have : 0 < ((N : ℝ) + 2) / ε := div_pos hNpos hε
    simp only [hLdef]; linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hεL : ε * L = ((N : ℝ) + 2) + ε := by
    simp only [hLdef]
    field_simp
  have hdiv : ((N : ℝ) + 2) / L < ε := by
    rw [div_lt_iff₀ hLpos]
    nlinarith
  have hone : (1 : ℝ) < ε * L := by
    rw [hεL]; linarith
  intro o hvalid hep
  have hcast : (((N + 2 : ℕ)) : ℝ) = (N : ℝ) + 2 := by push_cast; ring
  have hmoney : ∀ j, o.money j = (o.sold.card : ℝ) / ((N : ℝ) + 2) := by
    intro j
    rw [hep j, price_sum, hcast]
  by_cases hk : o.sold.card ≤ 1
  · -- few goods sold: agent `0` gets almost nothing
    refine ⟨0, ?_⟩
    rw [MMSEP_agent_zero N L hL1, mul_one, val_zero]
    have hcard : ((o.kept 0).card : ℝ) ≤ (N : ℝ) + 2 := by
      have := Finset.card_le_univ (o.kept 0)
      simp only [Fintype.card_fin] at this
      exact_mod_cast le_trans (by exact_mod_cast this) (le_of_eq (by push_cast; ring))
    have hsum : ∑ _g ∈ o.kept 0, (1 : ℝ) / L = ((o.kept 0).card : ℝ) * (1 / L) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hmon : o.money 0 ≤ 1 / ((N : ℝ) + 2) := by
      have hk' : (o.sold.card : ℝ) ≤ 1 := by exact_mod_cast hk
      rw [hmoney 0]
      gcongr
    unfold util
    rw [hsum]
    have h1 : ((o.kept 0).card : ℝ) * (1 / L) ≤ ((N : ℝ) + 2) / L := by
      rw [mul_one_div, div_le_div_iff_of_pos_right hLpos]
      exact hcard
    linarith
  · -- at least two goods sold: some agent other than `0` keeps nothing
    push_neg at hk
    have hRcard : ((Finset.univ : Finset (Fin (N + 2))) \ o.sold).card
        < ((Finset.univ : Finset (Fin (N + 2))) \ {(0 : Fin (N + 2))}).card := by
      have h1 : ((Finset.univ : Finset (Fin (N + 2))) \ o.sold).card = (N + 2) - o.sold.card := by
        simp [Finset.card_sdiff]
      have h2 : ((Finset.univ : Finset (Fin (N + 2))) \ {(0 : Fin (N + 2))}).card = N + 1 := by
        simp [Finset.card_sdiff]
      have h3 : o.sold.card ≤ N + 2 := by
        have := Finset.card_le_univ o.sold
        simpa using this
      omega
    obtain ⟨i, hiT, hi⟩ := exists_kept_subset o ∅ ((Finset.univ : Finset (Fin (N + 2))) \ o.sold)
      ((Finset.univ : Finset (Fin (N + 2))) \ {(0 : Fin (N + 2))}) hvalid.2.1
      (fun j => by
        intro g hg
        have hg' : g ∈ o.kept j := (Finset.mem_sdiff.mp hg).1
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        exact fun hgs => (Finset.disjoint_left.mp (hvalid.1 j) hgs) hg')
      hRcard
    have hi0 : i ≠ 0 := by
      have := (Finset.mem_sdiff.mp hiT).2
      simpa using this
    refine ⟨i, ?_⟩
    rw [MMSEP_agent_other N L hL1 hi0, val_ne_zero N L hi0]
    have hkept : o.kept i = ∅ := Finset.subset_empty.mp hi
    have hsold : (o.sold.card : ℝ) ≤ (N : ℝ) + 2 := by
      have := Finset.card_le_univ o.sold
      simp only [Fintype.card_fin] at this
      calc (o.sold.card : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast this
        _ = (N : ℝ) + 2 := hcast
    have hutil : util (fun _ => L) o i = (o.sold.card : ℝ) / ((N : ℝ) + 2) := by
      unfold util
      rw [hkept, hmoney i]
      simp
    rw [hutil]
    have h1 : (o.sold.card : ℝ) / ((N : ℝ) + 2) ≤ 1 := by
      rw [div_le_one hNpos]
      exact hsold
    have h2 : (1 : ℝ) < (1 / ((N : ℝ) + 2) + ε) * L := by
      have hle : ε ≤ 1 / ((N : ℝ) + 2) + ε := by
        have : (0 : ℝ) < 1 / ((N : ℝ) + 2) := by positivity
        linarith
      nlinarith
    linarith
end FairSelling.EqualProceedsExampleFour
