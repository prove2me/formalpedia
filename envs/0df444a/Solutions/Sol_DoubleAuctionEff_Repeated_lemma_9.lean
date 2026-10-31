-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:02:55.07283+00:00
-- url     : https://prove2.me/submissions/50595cc0-1695-47bc-adac-4cefd6813dea

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open DoubleAuctionEff.Repeated

namespace DAELemma9Aux

theorem u_ne_top {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (x : J → ℝ) : u x ≠ ⊤ := by
  intro h
  have hx : x ∈ dom u := by simp [dom, h]
  have := h1.2.2 x hx 1 one_pos
  rw [h] at this
  exact not_top_lt this

theorem le_indiff {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {r : ℝ}
    (h : u x0 ≤ u (x0 + y - r • g)) : (r : EReal) ≤ indiffPrice u g x0 y := by
  unfold indiffPrice
  exact le_iSup₂ (f := fun (r : ℝ) (_ : u x0 ≤ u (x0 + y - r • g)) => (r : EReal)) r h

theorem indiff_attained {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {c : ℝ}
    (husc : UpperSemicontinuous u) (hc : indiffPrice u g x0 y = (c : EReal)) :
    u x0 ≤ u (x0 + y - c • g) := by
  by_contra hlt
  push_neg at hlt
  have hcont : Continuous (fun r : ℝ => x0 + y - r • g) := by fun_prop
  have hev : ∀ᶠ r in nhds c, u (x0 + y - r • g) < u x0 :=
    hcont.continuousAt.eventually (husc _ _ hlt)
  rcases Metric.eventually_nhds_iff.1 hev with ⟨ε, hε, hball⟩
  have hle : indiffPrice u g x0 y ≤ ((c - ε : ℝ) : EReal) := by
    unfold indiffPrice
    refine iSup₂_le fun r hr => ?_
    have hrc : (r : EReal) ≤ c := hc ▸ le_indiff hr
    rw [EReal.coe_le_coe_iff] at hrc ⊢
    by_contra hcon
    push_neg at hcon
    have hd : dist r c < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    exact absurd hr (not_le.2 (hball hd))
  rw [hc, EReal.coe_le_coe_iff] at hle
  linarith

theorem coe_sum {I : Type*} (s : Finset I) (f : I → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, ih]

theorem split2 (a b : EReal) (t : ℝ) (h : (t : EReal) < a + b) :
    ∃ t1 t2 : ℝ, (t1 : EReal) < a ∧ (t2 : EReal) < b ∧ t ≤ t1 + t2 := by
  induction a using EReal.rec with
  | bot => simp at h
  | top =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => exact ⟨t, 0, EReal.coe_lt_top _, EReal.coe_lt_top _, by simp⟩
    | coe β => exact ⟨t - β + 1, β - 1, EReal.coe_lt_top _, by exact_mod_cast (by linarith),
        by linarith⟩
  | coe α =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => exact ⟨α - 1, t - α + 1, by exact_mod_cast (by linarith), EReal.coe_lt_top _,
        by linarith⟩
    | coe β =>
      rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h
      refine ⟨α - (α + β - t) / 2, β - (α + β - t) / 2, ?_, ?_, by linarith⟩ <;>
        exact_mod_cast (by linarith)

theorem split_sum {I : Type*} [DecidableEq I] (f : I → EReal) (s : Finset I) :
    ∀ t : ℝ, (t : EReal) < ∑ i ∈ s, f i →
      ∃ c : I → ℝ, (∀ i ∈ s, (c i : EReal) < f i) ∧ t ≤ ∑ i ∈ s, c i := by
  induction s using Finset.induction_on with
  | empty =>
    intro t ht
    refine ⟨0, by simp, ?_⟩
    simp only [Finset.sum_empty] at ht ⊢
    exact_mod_cast ht.le
  | insert j s hj ih =>
    intro t ht
    rw [Finset.sum_insert hj] at ht
    obtain ⟨t1, t2, h1, h2, h12⟩ := split2 _ _ t ht
    obtain ⟨c, hc, hcs⟩ := ih t2 h2
    refine ⟨Function.update c j t1, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa using h1
      · have : i ≠ j := fun h => hj (h ▸ hi)
        simpa [Function.update_of_ne this] using hc i hi
    · rw [Finset.sum_insert hj, Function.update_self]
      have : ∑ i ∈ s, Function.update c j t1 i = ∑ i ∈ s, c i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have : i ≠ j := fun h => hj (h ▸ hi)
        simp [Function.update_of_ne this]
      rw [this]; linarith

/-- Part 1 of Lemma 9: the optimum values of (P) and (P′) coincide. -/
theorem value_eq {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x0 : I → J → ℝ) :
    CS u g x0 = (⨆ (r : ℝ) (_ : ∃ w : I → J → ℝ, FeasibleP' u g x0 r w), (r : EReal)) := by
  apply le_antisymm
  · unfold CS
    refine iSup₂_le fun y hy => ?_
    by_contra hlt
    push_neg at hlt
    obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    obtain ⟨c, hc, hcs⟩ := split_sum (fun i => indiffPrice (u i) g (x0 i) (y i)) Finset.univ t ht2
    have hex : ∀ i, ∃ r' : ℝ, u i (x0 i) ≤ u i (x0 i + y i - r' • g) ∧ c i < r' := by
      intro i
      have := hc i (Finset.mem_univ i)
      unfold indiffPrice at this
      obtain ⟨r', hr'⟩ := lt_iSup_iff.1 this
      obtain ⟨hadm, hlt'⟩ := lt_iSup_iff.1 hr'
      exact ⟨r', hadm, by exact_mod_cast hlt'⟩
    choose r' hr'adm hr'gt using hex
    have hfeas : FeasibleP' u g x0 (∑ i, r' i) (fun i => x0 i + y i - r' i • g) := by
      refine ⟨?_, hr'adm⟩
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hy, ← Finset.sum_smul]
      abel
    have hle : ((∑ i, r' i : ℝ) : EReal) ≤
        ⨆ (r : ℝ) (_ : ∃ w : I → J → ℝ, FeasibleP' u g x0 r w), (r : EReal) :=
      le_iSup₂ (f := fun (r : ℝ) (_ : ∃ w : I → J → ℝ, FeasibleP' u g x0 r w) => (r : EReal))
        _ ⟨_, hfeas⟩
    have hlt2 : t < ∑ i, r' i :=
      lt_of_le_of_lt hcs (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        fun i _ => hr'gt i)
    have := lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlt2) hle
    exact absurd ht1 (not_lt.2 this.le)
  · refine iSup₂_le fun r ⟨w, hw⟩ => ?_
    set n : ℝ := (Fintype.card I : ℝ)
    have hn : 0 < n := by simp [n, Fintype.card_pos]
    set y : I → J → ℝ := fun i => w i - x0 i + (r / n) • g
    have hy : ∑ i, y i = 0 := by
      simp only [y, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        show (Fintype.card I : ℝ) * (r / n) = r by simp only [n]; field_simp, ← hw.1]
      abel
    have hD : ∀ i, ((r / n : ℝ) : EReal) ≤ indiffPrice (u i) g (x0 i) (y i) := by
      intro i
      apply le_indiff
      have : x0 i + y i - (r / n) • g = w i := by simp only [y]; abel
      rw [this]; exact hw.2 i
    have hsum : (r : EReal) ≤ ∑ i, indiffPrice (u i) g (x0 i) (y i) := by
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => hD i)
      rw [← coe_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      simp only [n]; field_simp
    unfold CS
    exact hsum.trans (le_iSup₂ (f := fun (y : I → J → ℝ) (_ : ∑ i, y i = 0) =>
      ∑ i, indiffPrice (u i) g (x0 i) (y i)) y hy)

end DAELemma9Aux

open DAELemma9Aux in
theorem solution {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J]
    [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x0 : I → J → ℝ) :
    CS u g x0 = (⨆ (r : ℝ) (_ : ∃ w : I → J → ℝ, FeasibleP' u g x0 r w), (r : EReal)) ∧
      ((∀ i, Assumption1 (u i) g) → ∀ xbar : I → J → ℝ,
        (SolvesP u g x0 xbar ∧ CS u g x0 ≠ ⊤) ↔
          ∃ r : I → ℝ, SolvesP' u g x0 (∑ i, r i) (fun i => x0 i + xbar i - r i • g)) := by
  have hval := value_eq u g x0
  refine ⟨hval, fun h1 xbar => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨hsum, hopt⟩, hne⟩
    -- CS equals the objective at xbar
    have hCS : CS u g x0 = ∑ i, indiffPrice (u i) g (x0 i) (xbar i) := by
      apply le_antisymm
      · unfold CS; exact iSup₂_le fun y hy => hopt y hy
      · unfold CS
        exact le_iSup₂ (f := fun (y : I → J → ℝ) (_ : ∑ i, y i = 0) =>
          ∑ i, indiffPrice (u i) g (x0 i) (y i)) xbar hsum
    have hnonneg : (0 : EReal) ≤ ∑ i, indiffPrice (u i) g (x0 i) (xbar i) := by
      refine le_trans ?_ (hopt 0 (by simp))
      refine Finset.sum_nonneg fun i _ => ?_
      have := le_indiff (u := u i) (g := g) (x0 := x0 i) (y := 0) (r := 0) (by simp)
      simpa using this
    -- each indifference price at xbar is finite
    have hfin : ∀ i, indiffPrice (u i) g (x0 i) (xbar i) ≠ ⊥ ∧
        indiffPrice (u i) g (x0 i) (xbar i) ≠ ⊤ := by
      intro i
      have hbot : ∀ j, indiffPrice (u j) g (x0 j) (xbar j) ≠ ⊥ := by
        intro j hj
        have : ∑ i, indiffPrice (u i) g (x0 i) (xbar i) = ⊥ := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj, EReal.bot_add]
        rw [this] at hnonneg
        exact absurd hnonneg (by simp)
      refine ⟨hbot i, fun hi => hne ?_⟩
      rw [hCS, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi]
      refine EReal.top_add_of_ne_bot ?_
      induction (Finset.univ.erase i) using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact EReal.add_ne_bot_iff.2 ⟨hbot j, ih⟩
    set r : I → ℝ := fun i => (indiffPrice (u i) g (x0 i) (xbar i)).toReal
    have hr : ∀ i, indiffPrice (u i) g (x0 i) (xbar i) = (r i : EReal) := fun i =>
      (EReal.coe_toReal (hfin i).2 (hfin i).1).symm
    refine ⟨r, ⟨?_, fun i => indiff_attained (h1 i).1 (hr i)⟩, fun r' w' hfeas => ?_⟩
    · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, ← Finset.sum_smul]
      abel
    · have h1' : (r' : EReal) ≤ CS u g x0 := by
        rw [hval]
        exact le_iSup₂ (f := fun (r : ℝ) (_ : ∃ w : I → J → ℝ, FeasibleP' u g x0 r w) =>
          (r : EReal)) r' ⟨w', hfeas⟩
      rw [hCS, Finset.sum_congr rfl fun i _ => hr i, ← coe_sum] at h1'
      exact_mod_cast h1'
  · rintro ⟨r, hfeas, hopt⟩
    have hsum : ∑ i, xbar i = 0 := by
      have := hfeas.1
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul] at this
      rw [sub_add_cancel] at this
      simpa using this
    have hCSle : CS u g x0 ≤ ((∑ i, r i : ℝ) : EReal) := by
      rw [hval]
      exact iSup₂_le fun r' ⟨w', hw'⟩ => EReal.coe_le_coe_iff.2 (hopt r' w' hw')
    have hD : ((∑ i, r i : ℝ) : EReal) ≤ ∑ i, indiffPrice (u i) g (x0 i) (xbar i) := by
      rw [coe_sum]
      exact Finset.sum_le_sum fun i _ => le_indiff (hfeas.2 i)
    refine ⟨⟨hsum, fun y hy => ?_⟩, ?_⟩
    · have : ∑ i, indiffPrice (u i) g (x0 i) (y i) ≤ CS u g x0 := by
        unfold CS
        exact le_iSup₂ (f := fun (y : I → J → ℝ) (_ : ∑ i, y i = 0) =>
          ∑ i, indiffPrice (u i) g (x0 i) (y i)) y hy
      exact this.trans (hCSle.trans hD)
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hCSle
