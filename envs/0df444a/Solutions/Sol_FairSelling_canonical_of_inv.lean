-- Prove2me | solution 1 for FairSelling.canonical_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:50.450591+00:00
-- url     : https://prove2.me/submissions/32f84e68-6b2e-45f3-89d9-16be4d87e0b5

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBudget
import Definitions.Def_RequestProject_TwoThirdsDescent
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Theorems.Thm_FairSelling_CanonExists_nonempty
import Theorems.Thm_FairSelling_Canonical_cash_nonneg
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_budget_ge_of_cover
import Theorems.Thm_FairSelling_descent
import Theorems.Thm_FairSelling_eventCost_le
import Theorems.Thm_FairSelling_eventCost_witness
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) {T : Finset (Fin n)} {R : Finset G} {D : ℝ} (hInv : Inv v p T R D)
    {i : Fin n} (hi : i ∈ T) (hmax : ∀ a ∈ T, MMS n (v a) p ≤ MMS n (v i) p)
    {k : ℕ} [NeZero k] (hk : T.card = k) :
    Nonempty (Canonical (v i) p (MMS n (v i) p) (thr v p i) k R D) := by
  classical
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  obtain ⟨hD, hL, hlt⟩ := hInv
  obtain ⟨alloc, sold, paid, hempty, hdisj1, hdisj2, hdisjR, hcover, hpaid0, hmoney, htypes⟩ := hL
  obtain ⟨E, hE⟩ := htypes i hi
  have hμ0 : 0 ≤ MMS n (v i) p := MMS_nonneg hn (v i) p (hv i) hp
  set ε : ℝ := MMS n (v i) p / 3 with hεdef
  have hε : 0 ≤ ε := by rw [hεdef]; linarith
  have h3ε : 3 * ε = MMS n (v i) p := by rw [hεdef]; ring
  have hthr : thr v p i = 2 * ε := by rw [thr, rho, hεdef]; ring
  have hthr' : thr v p i = 2 / 3 * MMS n (v i) p := by rw [thr, rho]
  -- the cost of each event, and its classification
  have hcostT : ∀ b ∈ T, eventCost E (alloc b) (sold b) (paid b) = 0 := by
    intro b hb
    obtain ⟨h1, h2, h3⟩ := hempty b hb
    rw [h1, h2, h3]
    simp [eventCost, vbarSum]
  have hcost_le : ∀ b ∉ T, eventCost E (alloc b) (sold b) (paid b) ≤ MMS n (v i) p := fun b hb =>
    eventCost_le E hp hμ0 hthr' (hdisj1 b) (hE b hb)
  have hdich : ∀ b ∉ T, eventCost E (alloc b) (sold b) (paid b) ≤ 2 * ε ∨
      ∃ x ∈ alloc b ∪ sold b, (∃ j, x ∈ E.part j) ∧
        eventCost E (alloc b) (sold b) (paid b) ≤ vbar (v i) p x + ε := by
    intro b hb
    have := eventCost_witness E hp hμ0 hthr' (hdisj1 b) (hE b hb)
    rwa [hthr, hεdef] at this
  -- the charged events, and their witnesses
  set Ch : Fin n → Prop := fun b => ∃ x ∈ alloc b ∪ sold b, (∃ j, x ∈ E.part j) ∧
      eventCost E (alloc b) (sold b) (paid b) ≤ vbar (v i) p x + ε with hChdef
  set Cs : Finset (Fin n) := (Finset.univ \ T).filter Ch with hCsdef
  set Chp : Finset (Fin n) := (Finset.univ \ T).filter (fun b => ¬ Ch b) with hChpdef
  set f : Fin n → Finset G := fun b => if h : Ch b then {Classical.choose h} else ∅ with hfdef
  set Qs : Finset G := Cs.biUnion f with hQsdef
  have hfCh : ∀ (b : Fin n) (h : Ch b), f b = {Classical.choose h} := by
    intro b h; rw [hfdef]; simp only [dif_pos h]
  have hfsub : ∀ b, f b ⊆ alloc b ∪ sold b := by
    intro b g hg
    by_cases h : Ch b
    · rw [hfCh b h, Finset.mem_singleton] at hg
      rw [hg]
      exact (Classical.choose_spec h).1
    · rw [hfdef] at hg; simp only [dif_neg h, Finset.notMem_empty] at hg
  have hfdisj : ∀ b ∈ Cs, ∀ b' ∈ Cs, b ≠ b' → Disjoint (f b) (f b') := by
    intro b _ b' _ hbb
    exact Finset.disjoint_of_subset_left (hfsub b)
      (Finset.disjoint_of_subset_right (hfsub b') (hdisj2 b b' hbb))
  have hCsCh : ∀ b ∈ Cs, Ch b := fun b hb => (Finset.mem_filter.mp hb).2
  have hCsT : ∀ b ∈ Cs, b ∉ T := by
    intro b hb
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).2
  have hfcard : ∀ b ∈ Cs, (f b).card = 1 := by
    intro b hb
    rw [hfCh b (hCsCh b hb), Finset.card_singleton]
  have hQcard : Qs.card = Cs.card := by
    rw [hQsdef, Finset.card_biUnion hfdisj, Finset.sum_congr rfl hfcard, Finset.sum_const,
      smul_eq_mul, mul_one]
  -- the credits
  set cred : G → ℝ := fun g => min (3 * ε) (vbar (v i) p g + ε) with hcreddef
  set bidx : G → Fin n :=
    fun g => if h : ∃ j, g ∈ E.part j then Classical.choose h else ⟨0, hn⟩ with hbidxdef
  have hQpart : ∀ g ∈ Qs, ∃ j, g ∈ E.part j := by
    intro g hg
    obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.mp hg
    rw [hfCh b (hCsCh b hb), Finset.mem_singleton] at hgb
    rw [hgb]
    exact (Classical.choose_spec (hCsCh b hb)).2.1
  have hQbidx : ∀ g ∈ Qs, g ∈ E.part (bidx g) := by
    intro g hg
    have h := hQpart g hg
    simp only [hbidxdef, dif_pos h]
    exact Classical.choose_spec h
  have hQR : ∀ g ∈ Qs, g ∉ R := by
    intro g hg
    obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.mp hg
    exact fun hgR => Finset.disjoint_left.mp (hdisjR b) hgR (hfsub b hgb)
  -- the total cost of the events
  have hcostCs : ∀ b ∈ Cs, eventCost E (alloc b) (sold b) (paid b) ≤ ∑ g ∈ f b, cred g := by
    intro b hb
    have h := hCsCh b hb
    rw [hfCh b h, Finset.sum_singleton]
    simp only [hcreddef]
    refine le_min ?_ (Classical.choose_spec h).2.2
    rw [h3ε]
    exact hcost_le b (hCsT b hb)
  have hcostChp : ∀ b ∈ Chp, eventCost E (alloc b) (sold b) (paid b) ≤ 2 * ε := by
    intro b hb
    have hbT : b ∉ T := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).2
    rcases hdich b hbT with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.mp hb).2
  have hsumQs : ∑ g ∈ Qs, cred g = ∑ b ∈ Cs, ∑ g ∈ f b, cred g := by
    rw [hQsdef, Finset.sum_biUnion]
    intro b hb b' hb' hbb
    exact hfdisj b hb b' hb' hbb
  have hsumcost : ∑ b, eventCost E (alloc b) (sold b) (paid b)
      ≤ (Chp.card : ℝ) * (2 * ε) + ∑ g ∈ Qs, cred g := by
    have hsplit : (∑ b ∈ Finset.univ \ T, eventCost E (alloc b) (sold b) (paid b))
        + ∑ b ∈ T, eventCost E (alloc b) (sold b) (paid b)
        = ∑ b, eventCost E (alloc b) (sold b) (paid b) :=
      Finset.sum_sdiff (Finset.subset_univ T)
    have hT0 : ∑ b ∈ T, eventCost E (alloc b) (sold b) (paid b) = 0 :=
      Finset.sum_eq_zero hcostT
    have hsplit2 : (∑ b ∈ Cs, eventCost E (alloc b) (sold b) (paid b))
        + ∑ b ∈ Chp, eventCost E (alloc b) (sold b) (paid b)
        = ∑ b ∈ Finset.univ \ T, eventCost E (alloc b) (sold b) (paid b) := by
      rw [hCsdef, hChpdef]
      exact Finset.sum_filter_add_sum_filter_not _ _ _
    have hA : (∑ b ∈ Cs, eventCost E (alloc b) (sold b) (paid b)) ≤ ∑ g ∈ Qs, cred g := by
      rw [hsumQs]
      exact Finset.sum_le_sum hcostCs
    have hB : (∑ b ∈ Chp, eventCost E (alloc b) (sold b) (paid b)) ≤ (Chp.card : ℝ) * (2 * ε) := by
      calc (∑ b ∈ Chp, eventCost E (alloc b) (sold b) (paid b)) ≤ ∑ _b ∈ Chp, (2 * ε) :=
            Finset.sum_le_sum hcostChp
        _ = (Chp.card : ℝ) * (2 * ε) := by rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  -- the budget of the agent
  have hbud := budget_ge_of_cover E R D alloc sold paid hdisj2 hdisjR hcover hmoney
  rw [EquiMMS.budget] at hbud
  -- the counting
  have hcount : T.card + Chp.card + Qs.card = (Finset.univ : Finset (Fin n)).card := by
    have h1 : Cs.card + Chp.card = (Finset.univ \ T).card := by
      rw [hCsdef, hChpdef]
      exact Finset.card_filter_add_card_filter_not _
    have h2 : ((Finset.univ : Finset (Fin n)) \ T).card = n - T.card := by
      rw [Finset.card_univ_diff, Fintype.card_fin]
    have h3 : T.card ≤ n := by simpa using Finset.card_le_univ T
    have h4 : (Finset.univ : Finset (Fin n)).card = n := by simp
    omega
  -- the descent
  have hcanon := descent (v i) p hp hε E.part (fun g => g) bidx cred (E.sell ∩ R) D hD
    (fun g hg => E.sell_price g (Finset.mem_inter.mp hg).1)
    E.part_disj
    (fun j => Finset.disjoint_of_subset_left Finset.inter_subset_left (E.sell_disj j))
    (by
      intro j
      have h1 := E.value j
      have h2 := E.cash_nonneg j
      rw [h3ε]
      linarith)
    n R Finset.univ Qs T.card Chp.card (by simp)
    Finset.inter_subset_right
    (by
      intro g hg
      have := hlt i hi g hg
      rw [hthr] at this
      linarith)
    hQbidx
    (fun g _ => by simp only [hcreddef]; exact min_le_left _ _)
    (fun g _ => by simp only [hcreddef]; exact min_le_right _ _)
    hQR
    (fun x _ y _ h => h)
    (fun g _ => Finset.mem_univ _)
    (by rw [hcount])
    (by
      have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by simp
      rw [hcard, h3ε]
      linarith)
  rw [hk] at hcanon
  have hres := hcanon.nonempty
  rw [h3ε, ← hthr] at hres
  exact hres
end FairSelling
