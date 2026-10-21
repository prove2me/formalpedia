-- Prove2me | solution 1 for ExAnteExPost.RPS.implements_rps_succ
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T08:37:26.39031+00:00
-- url     : https://prove2.me/submissions/c5314c56-314d-49ca-8c03-98bd61e80b61

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

open Finset ExAnteExPost.RPS

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace RPSAux

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- The goods with positive remaining mass. -/
noncomputable def avail (s : EatState N G) : Finset G := univ.filter fun g => 0 < s.rem g

lemma step_inactive [Nonempty N] (pick : PickRule N G) (s : EatState N G)
    (h : ¬ (0 < s.τ ∧ (avail s).Nonempty)) : eatStep pick s = s := by
  exact dif_neg h

lemma step_active [Nonempty N] (pick : PickRule N G)
    (hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S) (s : EatState N G)
    (h : 0 < s.τ ∧ (avail s).Nonempty) :
    ∃ (e : N → G) (δ : ℝ), (∀ i, e i ∈ avail s) ∧ (∀ i, e i = pick i (avail s) h.2) ∧
      0 < δ ∧ δ ≤ s.τ ∧
      (∀ g, ((univ.filter fun j => e j = g).card : ℝ) * δ ≤ s.rem g ∨
          (univ.filter fun j => e j = g).card = 0) ∧
      (δ = s.τ ∨ ∃ g0, (∃ i, e i = g0) ∧
          ((univ.filter fun j => e j = g0).card : ℝ) * δ = s.rem g0) ∧
      eatStep pick s = ⟨fun g => s.rem g - (univ.filter fun i => e i = g).card * δ,
          fun i g => s.X i g + if e i = g then δ else 0, s.τ - δ⟩ := by
  set e : N → G := fun i => pick i (avail s) h.2 with he
  set k : G → ℕ := fun g => (univ.filter fun i => e i = g).card with hk
  have hne : (univ.image e).Nonempty := univ_nonempty.image e
  set m : ℝ := (univ.image e).inf' hne fun g => s.rem g / k g with hm
  have heav : ∀ i, e i ∈ avail s := fun i => hmem i _ _
  have hkpos : ∀ i, (0 : ℝ) < k (e i) := by
    intro i
    have : i ∈ univ.filter fun j => e j = e i := by simp
    have : 0 < k (e i) := Finset.card_pos.mpr ⟨i, this⟩
    exact_mod_cast this
  have hrempos : ∀ i, 0 < s.rem (e i) := by
    intro i; have := heav i; simp [avail] at this; exact this
  have hmpos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    exact div_pos (hrempos i) (hkpos i)
  refine ⟨e, min s.τ m, heav, fun i => rfl, lt_min h.1 hmpos, min_le_left _ _, ?_, ?_, ?_⟩
  · intro g
    by_cases hg : ∃ i, e i = g
    · left
      obtain ⟨i, rfl⟩ := hg
      have h1 : min s.τ m ≤ s.rem (e i) / k (e i) := by
        refine (min_le_right _ _).trans ?_
        exact Finset.inf'_le _ (Finset.mem_image_of_mem e (mem_univ i))
      have := (le_div_iff₀ (hkpos i)).mp h1
      simpa [hk, mul_comm] using this
    · right
      push Not at hg
      simp [Finset.filter_eq_empty_iff, hg]
  · rcases min_choice s.τ m with h1 | h1
    · left; exact h1
    · right
      obtain ⟨g0, hg0, hg0eq⟩ := Finset.exists_mem_eq_inf' hne fun g => s.rem g / k g
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hg0
      refine ⟨e i, ⟨i, rfl⟩, ?_⟩
      rw [h1, hm, hg0eq]
      have := (hkpos i).ne'
      simp only [hk] at this ⊢
      field_simp
  · exact dif_pos h

/-- Basic invariants of the eating protocol. -/
structure Inv (M' : Finset G) (s : EatState N G) : Prop where
  rem_nn : ∀ g, 0 ≤ s.rem g
  X_nn : ∀ i g, 0 ≤ s.X i g
  τ_nn : 0 ≤ s.τ
  col : ∀ g, s.rem g + ∑ i, s.X i g = if g ∈ M' then 1 else 0
  row : ∀ i, ∑ g, s.X i g + s.τ = 1

noncomputable def s0 (M' : Finset G) : EatState N G :=
  ⟨fun g => if g ∈ M' then 1 else 0, fun _ _ => 0, 1⟩

noncomputable def st [Nonempty N] (pick : PickRule N G) (M' : Finset G) (j : ℕ) :
    EatState N G := (eatStep pick)^[j] (s0 M')

lemma eating_eq [Nonempty N] (pick : PickRule N G) (M' : Finset G) :
    eating pick M' = (st pick M' (Fintype.card G + 1)).X := rfl

lemma st_succ [Nonempty N] (pick : PickRule N G) (M' : Finset G) (j : ℕ) :
    st pick M' (j + 1) = eatStep pick (st pick M' j) := by
  simp only [st]; rw [Function.iterate_succ_apply']

lemma inv_s0 (M' : Finset G) : Inv M' (s0 M' : EatState N G) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp [s0] <;> split_ifs <;> norm_num

lemma sum_ite_card (e : N → G) (δ : ℝ) (g : G) :
    ∑ i, (if e i = g then δ else 0) = ((univ.filter fun i => e i = g).card : ℝ) * δ := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

lemma inv_step [Nonempty N] (pick : PickRule N G)
    (hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S) (M' : Finset G) (s : EatState N G)
    (hs : Inv M' s) : Inv M' (eatStep pick s) := by
  by_cases h : 0 < s.τ ∧ (avail s).Nonempty
  · obtain ⟨e, δ, -, -, hδ, hδτ, hk, -, heq⟩ := step_active pick hmem s h
    rw [heq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g
      rcases hk g with h1 | h1
      · simp only; linarith
      · simp only [h1]; simp [hs.rem_nn g]
    · intro i g
      simp only
      have := hs.X_nn i g
      split_ifs <;> linarith
    · simp only; linarith
    · intro g
      simp only
      rw [Finset.sum_add_distrib, sum_ite_card, ← hs.col g]
      ring
    · intro i
      simp only
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (mem_univ _), ← hs.row i]
      ring
  · rw [step_inactive pick s h]; exact hs

lemma inv_st [Nonempty N] (pick : PickRule N G)
    (hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S) (M' : Finset G) (j : ℕ) :
    Inv M' (st pick M' j) := by
  induction j with
  | zero => exact inv_s0 M'
  | succ j ih => rw [st_succ]; exact inv_step pick hmem M' _ ih

/-- Each active step either uses up the remaining time or exhausts a good. -/
lemma step_progress [Nonempty N] (pick : PickRule N G)
    (hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S) (M' : Finset G)
    (hM : Fintype.card N ≤ M'.card) (s : EatState N G) (hs : Inv M' s) (hτ : 0 < s.τ) :
    (eatStep pick s).τ = 0 ∨ (avail (eatStep pick s)).card < (avail s).card := by
  by_cases hav : (avail s).Nonempty
  · obtain ⟨e, δ, -, -, hδ, hδτ, hk, hch, heq⟩ := step_active pick hmem s ⟨hτ, hav⟩
    rw [heq]
    rcases hch with h1 | ⟨g0, ⟨i0, hi0⟩, hg0⟩
    · left; simp [h1]
    · right
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨g0, ?_, ?_⟩
        · simp only [avail, mem_filter, mem_univ, true_and]
          -- rem g0 = k * δ > 0
          rw [← hg0]
          have : (0 : ℝ) < (univ.filter fun j => e j = g0).card := by
            have : i0 ∈ univ.filter fun j => e j = g0 := by simp [hi0]
            exact_mod_cast Finset.card_pos.mpr ⟨i0, this⟩
          positivity
        · simp only [avail, mem_filter, mem_univ, true_and, not_lt]
          rw [← hg0]; linarith
      · intro g hg
        simp only [avail, mem_filter, mem_univ, true_and] at hg ⊢
        rcases hk g with h1 | h1
        · -- rem g - k δ ≥ ... we need positivity: rem g - k δ > 0 → rem g > 0
          have : (0 : ℝ) ≤ ((univ.filter fun j => e j = g).card : ℝ) * δ := by positivity
          linarith
        · simp only [h1] at hg; simpa using hg
  · exfalso
    -- all remaining masses are zero
    have hrem0 : ∀ g, s.rem g = 0 := by
      intro g
      have := hs.rem_nn g
      by_contra hne
      exact hav ⟨g, by simp [avail]; exact lt_of_le_of_ne this (Ne.symm hne)⟩
    have h1 : ∑ g, ∑ i, s.X i g = (M'.card : ℝ) := by
      have : ∀ g, ∑ i, s.X i g = if g ∈ M' then 1 else 0 := by
        intro g; have := hs.col g; rw [hrem0 g] at this; linarith
      simp only [this]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ i, ∑ g, s.X i g = (Fintype.card N : ℝ) * (1 - s.τ) := by
      have : ∀ i, ∑ g, s.X i g = 1 - s.τ := by
        intro i; have := hs.row i; linarith
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_comm] at h1
    have hn : (0 : ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
    have hM' : (Fintype.card N : ℝ) ≤ M'.card := by exact_mod_cast hM
    nlinarith

lemma st_tau_or [Nonempty N] (pick : PickRule N G)
    (hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S) (M' : Finset G)
    (hM : Fintype.card N ≤ M'.card) (j : ℕ) :
    (st pick M' j).τ = 0 ∨ (avail (st pick M' j)).card + j ≤ Fintype.card G := by
  induction j with
  | zero => right; simpa using Finset.card_le_univ _
  | succ j ih =>
    rw [st_succ]
    have hinv := inv_st pick hmem M' j
    rcases ih with h0 | h0
    · left
      rw [step_inactive pick _ (by intro h; linarith [h.1])]; exact h0
    · by_cases h0' : (st pick M' j).τ = 0
      · left
        rw [step_inactive pick _ (by intro h; linarith [h.1])]; exact h0'
      · have hτ : 0 < (st pick M' j).τ := lt_of_le_of_ne hinv.τ_nn (Ne.symm h0')
        rcases step_progress pick hmem M' hM _ hinv hτ with h1 | h1
        · left; exact h1
        · right; omega

lemma final_tau [Nonempty N] (pick : PickRule N G)
    (hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S) (M' : Finset G)
    (hM : Fintype.card N ≤ M'.card) : (st pick M' (Fintype.card G + 1)).τ = 0 := by
  rcases st_tau_or pick hmem M' hM (Fintype.card G + 1) with h | h
  · exact h
  · omega

/-- Everything about one eating stage that the later proofs use. -/
theorem eating_props [Nonempty N] (pick : PickRule N G)
    (hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S) (M' : Finset G) :
    BvNInput (eating pick M') ∧ (∀ i g, g ∉ M' → eating pick M' i g = 0) ∧
      (Fintype.card N ≤ M'.card → ∀ i, ∑ g, eating pick M' i g = 1) := by
  have hinv := inv_st pick hmem M' (Fintype.card G + 1)
  rw [eating_eq]
  set s := st pick M' (Fintype.card G + 1)
  have hcol : ∀ g, ∑ i, s.X i g ≤ 1 := by
    intro g; have := hinv.col g; have := hinv.rem_nn g; split_ifs at * <;> linarith
  have hrow : ∀ i, ∑ g, s.X i g ≤ 1 := by
    intro i; have := hinv.row i; have := hinv.τ_nn; linarith
  refine ⟨⟨fun i g => ⟨hinv.X_nn i g, ?_⟩, hrow, hcol⟩, ?_, ?_⟩
  · refine le_trans ?_ (hrow i)
    exact Finset.single_le_sum (fun g _ => hinv.X_nn i g) (mem_univ g)
  · intro i g hg
    have h1 := hinv.col g
    rw [if_neg hg] at h1
    have h2 := hinv.rem_nn g
    have h3 : ∑ j, s.X j g = 0 := by
      have : 0 ≤ ∑ j, s.X j g := Finset.sum_nonneg fun j _ => hinv.X_nn j g
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hinv.X_nn j g).mp h3 i (mem_univ i)
  · intro hM i
    have := hinv.row i
    rw [final_tau pick hmem M' hM] at this
    linarith

lemma util_step (I : Instance N G) (i : N) (x : G → ℝ) (g0 : G) (δ : ℝ) :
    util I i (fun g => x g + if g0 = g then δ else 0) = util I i x + δ * I.v i g0 := by
  simp only [util, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    if_pos (mem_univ _)]

/-- The eating allocation is envy-free (at every intermediate state). -/
lemma ef_st [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (M' : Finset G) (j : ℕ) :
    ∀ i h, util I i ((st pick M' j).X h) ≤ util I i ((st pick M' j).X i) := by
  have hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S := fun i S hS => (hpick i S hS).1
  induction j with
  | zero => intro i h; simp [st, s0, util]
  | succ j ih =>
    intro i h
    rw [st_succ]
    set s := st pick M' j
    by_cases hact : 0 < s.τ ∧ (avail s).Nonempty
    · obtain ⟨e, δ, hav, he, hδ, -, -, -, heq⟩ := step_active pick hmem s hact
      rw [heq]
      simp only
      rw [util_step, util_step]
      have h1 := ih i h
      have h2 : I.v i (e h) ≤ I.v i (e i) := by
        rw [he i]; exact (hpick i _ hact.2).2 _ (hav h)
      nlinarith
    · rw [step_inactive pick s hact]; exact ih i h

theorem eating_ef [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (M' : Finset G) : IsEF I (eating pick M') := by
  intro i h; rw [eating_eq]; exact ef_st I pick hpick M' _ i h

/-- Whenever agent `i` eats a good `g` while `g'` is still available, she values `g` at least as
much as `g'`. -/
lemma fav_st [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (M' : Finset G) (i : N) (g' : G) (j : ℕ) :
    (st pick M' j).rem g' ≤ 0 ∨ ∀ g, 0 < (st pick M' j).X i g → I.v i g' ≤ I.v i g := by
  have hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S := fun i S hS => (hpick i S hS).1
  induction j with
  | zero => right; intro g hg; simp [st, s0] at hg
  | succ j ih =>
    rw [st_succ]
    set s := st pick M' j
    by_cases hact : 0 < s.τ ∧ (avail s).Nonempty
    · obtain ⟨e, δ, hav, he, hδ, -, -, -, heq⟩ := step_active pick hmem s hact
      rw [heq]
      simp only
      by_cases hr : s.rem g' ≤ 0
      · left
        have : (0 : ℝ) ≤ ((univ.filter fun j => e j = g').card : ℝ) * δ := by positivity
        linarith
      · right
        rcases ih with ih | ih
        · exact absurd ih hr
        intro g hg
        by_cases hei : e i = g
        · subst hei
          rw [he i]
          refine (hpick i _ hact.2).2 _ ?_
          simp only [avail, mem_filter, mem_univ, true_and]; linarith
        · rw [if_neg hei, add_zero] at hg
          exact ih g hg
    · rw [step_inactive pick s hact]; exact ih

/-- If `g' ∈ M'` is not fully eaten in the stage, then every good agent `i` eats has value at
least that of `g'` for `i`. -/
theorem eating_fav [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (M' : Finset G) (i : N) (g' : G) (hg' : g' ∈ M')
    (hcol : ∑ j, eating pick M' j g' < 1) (g : G) (hg : 0 < eating pick M' i g) :
    I.v i g' ≤ I.v i g := by
  have hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S := fun i S hS => (hpick i S hS).1
  rw [eating_eq] at hcol hg
  rcases fav_st I pick hpick M' i g' (Fintype.card G + 1) with h | h
  · have := (inv_st pick hmem M' (Fintype.card G + 1)).col g'
    rw [if_pos hg'] at this
    linarith
  · exact h g hg

end RPSAux

namespace RPSAux

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-! ### Consequences of the Theorem 1 conclusions for one eating stage -/

section Stage

variable [Nonempty N] (pick : PickRule N G) (hmem : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S)
  (M' : Finset G) (d : Decomp N G) (hd : IsBvNDecomp (eating pick M') d)
include hmem hd

lemma dec_w (k : Fin d.q) : 0 ≤ d.w k ∧ d.w k ≤ 1 := hd.1 k

lemma dec_holders_le (k : Fin d.q) (g : G) : (holders (d.A k) g).card ≤ 1 := by
  have h1 := (hd.2.2.2.2 k g).2
  have h2 : ⌈∑ i, eating pick M' i g⌉ ≤ 1 := Int.ceil_le.mpr (by
    have := ((eating_props pick hmem M').1.2.2 g); exact_mod_cast this)
  have : ((holders (d.A k) g).card : ℤ) ≤ 1 := h1.trans h2
  exact_mod_cast this

lemma dec_disj (k : Fin d.q) : IsIntAlloc (d.A k) := by
  intro i h hih
  rw [Finset.disjoint_left]
  intro g hgi hgh
  have := dec_holders_le pick hmem M' d hd k g
  have hi : i ∈ holders (d.A k) g := by simp [holders, hgi]
  have hh : h ∈ holders (d.A k) g := by simp [holders, hgh]
  exact hih (Finset.card_le_one.mp this i hi h hh)

lemma dec_sub (k : Fin d.q) (i : N) : d.A k i ⊆ M' := by
  intro g hg
  by_contra hgM
  have h1 := (hd.2.2.2.2 k g).2
  have h0 : ∑ j, eating pick M' j g = 0 :=
    Finset.sum_eq_zero fun j _ => (eating_props pick hmem M').2.1 j g hgM
  rw [h0, Int.ceil_zero] at h1
  have : i ∈ holders (d.A k) g := by simp [holders, hg]
  have : 0 < (holders (d.A k) g).card := Finset.card_pos.mpr ⟨i, this⟩
  omega

lemma dec_card_le (k : Fin d.q) (i : N) : (d.A k i).card ≤ 1 := by
  have h1 := (hd.2.2.2.1 k i).2
  have h2 : ⌈∑ g, eating pick M' i g⌉ ≤ 1 := Int.ceil_le.mpr (by
    have := ((eating_props pick hmem M').1.2.1 i); exact_mod_cast this)
  have : ((d.A k i).card : ℤ) ≤ 1 := h1.trans h2
  exact_mod_cast this

lemma dec_card_eq (hM : Fintype.card N ≤ M'.card) (k : Fin d.q) (i : N) :
    (d.A k i).card = 1 := by
  have h1 := (hd.2.2.2.1 k i)
  rw [(eating_props pick hmem M').2.2 hM i] at h1
  obtain ⟨h1a, h1b⟩ := h1
  simp only [Int.floor_one, Int.ceil_one] at h1a h1b
  omega

lemma dec_col_lt (k : Fin d.q) (g : G) (hg : g ∉ univ.biUnion (d.A k)) :
    ∑ j, eating pick M' j g < 1 := by
  have h1 := (hd.2.2.2.2 k g).1
  have : holders (d.A k) g = ∅ := by
    ext j; simp only [holders, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro hj; exact hg (Finset.mem_biUnion.mpr ⟨j, mem_univ _, hj⟩)
  rw [this, Finset.card_empty, Nat.cast_zero] at h1
  have := Int.floor_lt.mp (show ⌊∑ j, eating pick M' j g⌋ < (1 : ℤ) by omega)
  exact_mod_cast this

lemma dec_eat_ge (k : Fin d.q) (i : N) (g : G) (hg : g ∈ d.A k i) :
    d.w k ≤ eating pick M' i g := by
  rw [hd.2.2.1 i g]
  have : d.w k = d.w k * toFrac (d.A k) i g := by simp [toFrac, hg]
  rw [this]
  exact Finset.single_le_sum (f := fun k => d.w k * toFrac (d.A k) i g)
    (fun k' _ => mul_nonneg (dec_w pick hmem M' d hd k').1 (by unfold toFrac; split_ifs <;> norm_num))
    (mem_univ k)

lemma dec_card_union (hM : Fintype.card N ≤ M'.card) (k : Fin d.q) :
    (M' \ univ.biUnion (d.A k)).card + Fintype.card N = M'.card := by
  have hsub : univ.biUnion (d.A k) ⊆ M' := by
    intro g hg
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hg
    exact dec_sub pick hmem M' d hd k i hi
  have hcard : (univ.biUnion (d.A k)).card = Fintype.card N := by
    rw [Finset.card_biUnion]
    · simp [dec_card_eq pick hmem M' d hd hM k]
    · intro i _ j _ hij; exact dec_disj pick hmem M' d hd k i j hij
  rw [Finset.card_sdiff_of_subset hsub, hcard]
  exact Nat.sub_add_cancel hM

end Stage

/-! ### Histories -/

lemma unionHist_cons (A : IntAlloc N G) (H : List (IntAlloc N G)) (i : N) :
    unionHist (A :: H) i = A i ∪ unionHist H i := rfl

lemma unionHist_nil (i : N) : unionHist ([] : List (IntAlloc N G)) i = ∅ := rfl

lemma mem_hist_succ [Nonempty N] (pick : PickRule N G) (D : FracAlloc N G → Decomp N G)
    (T : ℕ) (M' : Finset G) (e : ℝ × List (IntAlloc N G)) :
    e ∈ rpsHist pick D (T + 1) M' ↔ ∃ k, ∃ e' ∈ rpsHist pick D T
      (M' \ univ.biUnion ((D (eating pick M')).A k)),
        e = ((D (eating pick M')).w k * e'.1, (D (eating pick M')).A k :: e'.2) := by
  simp only [rpsHist, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨k, e', h1, rfl⟩; exact ⟨k, e', h1, rfl⟩
  · rintro ⟨k, e', h1, rfl⟩; exact ⟨k, e', h1, rfl⟩

lemma mem_hist_zero [Nonempty N] (pick : PickRule N G) (D : FracAlloc N G → Decomp N G)
    (M' : Finset G) (e : ℝ × List (IntAlloc N G)) :
    e ∈ rpsHist pick D 0 M' ↔ e = (1, []) := by
  simp [rpsHist]

lemma list_sum_flatMap {α β : Type*} (l : List α) (f : α → List β) (F : β → ℝ) :
    ((l.flatMap f).map F).sum = (l.map fun a => ((f a).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma list_aux {β : Type*} (L : List (ℝ × β)) (c x : ℝ) (f : ℝ × β → ℝ) :
    (L.map fun e => c * e.1 * (x + f e)).sum =
      c * x * (L.map fun e => e.1).sum + c * (L.map fun e => e.1 * f e).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma sum_hist_succ [Nonempty N] (pick : PickRule N G) (D : FracAlloc N G → Decomp N G)
    (T : ℕ) (M' : Finset G) (F : ℝ × List (IntAlloc N G) → ℝ) :
    ((rpsHist pick D (T + 1) M').map F).sum = ∑ k, ((rpsHist pick D T
      (M' \ univ.biUnion ((D (eating pick M')).A k))).map fun e' =>
        F ((D (eating pick M')).w k * e'.1, (D (eating pick M')).A k :: e'.2)).sum := by
  rw [Fin.sum_univ_def]
  simp only [rpsHist]
  rw [list_sum_flatMap]
  simp [List.map_map, Function.comp_def]

section Main

variable [Nonempty N] (I : Instance N G) (pick : PickRule N G) (hpick : IsFavoritePick I pick)
  (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D)
include hpick hD

lemma hmem_of : ∀ i S (hS : S.Nonempty), pick i S hS ∈ S := fun i S hS => (hpick i S hS).1

lemma hdec (M' : Finset G) : IsBvNDecomp (eating pick M') (D (eating pick M')) :=
  hD _ (eating_props pick (hmem_of I pick hpick D hD) M').1

/-- Basic facts on histories: probabilities in `[0,1]`, disjoint bundles inside `M'`, total
probability one. -/
theorem hist_basic (T : ℕ) : ∀ M' : Finset G,
    (∀ e ∈ rpsHist pick D T M', (0 ≤ e.1 ∧ e.1 ≤ 1) ∧ IsIntAlloc (unionHist e.2) ∧
      ∀ i, unionHist e.2 i ⊆ M') ∧ ((rpsHist pick D T M').map Prod.fst).sum = 1 := by
  have hmem := hmem_of I pick hpick D hD
  induction T with
  | zero =>
    intro M'
    refine ⟨?_, by simp [rpsHist]⟩
    intro e he
    rw [mem_hist_zero] at he; subst he
    refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · intro i h _; simp [unionHist_nil]
    · intro i; simp [unionHist_nil]
  | succ T ih =>
    intro M'
    set d := D (eating pick M')
    have hd : IsBvNDecomp (eating pick M') d := hdec I pick hpick D hD M'
    refine ⟨?_, ?_⟩
    · intro e he
      rw [mem_hist_succ] at he
      obtain ⟨k, e', he', rfl⟩ := he
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (ih _).1 e' he'
      have hw := dec_w pick hmem M' d hd k
      refine ⟨⟨mul_nonneg hw.1 h1, ?_⟩, ?_, ?_⟩
      · calc d.w k * e'.1 ≤ 1 * 1 := mul_le_mul hw.2 h2 h1 (by norm_num)
          _ = 1 := by norm_num
      · intro i h hih
        simp only [unionHist_cons]
        rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
        refine ⟨⟨dec_disj pick hmem M' d hd k i h hih, ?_⟩, ?_, h3 i h hih⟩
        · rw [Finset.disjoint_right]
          intro g hg hgi
          have := h4 h hg
          simp only [mem_sdiff, Finset.mem_biUnion, mem_univ, true_and, not_exists] at this
          exact this.2 i hgi
        · rw [Finset.disjoint_left]
          intro g hg hgi
          have := h4 i hg
          simp only [mem_sdiff, Finset.mem_biUnion, mem_univ, true_and, not_exists] at this
          exact this.2 h hgi
      · intro i
        simp only [unionHist_cons]
        refine Finset.union_subset (dec_sub pick hmem M' d hd k i) ?_
        exact (h4 i).trans Finset.sdiff_subset
    · rw [sum_hist_succ]
      have : ∀ k, ((rpsHist pick D T (M' \ univ.biUnion (d.A k))).map fun e' =>
          (d.w k * e'.1, d.A k :: e'.2).1).sum = d.w k := by
        intro k
        have := (ih (M' \ univ.biUnion (d.A k))).2
        simp only
        rw [List.sum_map_mul_left, this, mul_one]
      simp only [d] at this ⊢
      rw [Finset.sum_congr rfl fun k _ => this k]
      exact hd.2.1

/-- Disjoint union in `toFrac`. -/
lemma toFrac_cons (T : ℕ) (M' : Finset G) (k : Fin (D (eating pick M')).q)
    (e' : ℝ × List (IntAlloc N G))
    (he' : e' ∈ rpsHist pick D T (M' \ univ.biUnion ((D (eating pick M')).A k))) (i : N) (g : G) :
    toFrac (unionHist ((D (eating pick M')).A k :: e'.2)) i g =
      toFrac ((D (eating pick M')).A k) i g + toFrac (unionHist e'.2) i g := by
  have h4 := ((hist_basic I pick hpick D hD T _).1 e' he').2.2 i
  simp only [toFrac, unionHist_cons, Finset.mem_union]
  by_cases h1 : g ∈ (D (eating pick M')).A k i
  · have : g ∉ unionHist e'.2 i := by
      intro hg
      have := h4 hg
      simp only [mem_sdiff, Finset.mem_biUnion, mem_univ, true_and, not_exists] at this
      exact this.2 i h1
    simp [h1, this]
  · simp [h1]

theorem implements_succ (T : ℕ) (M' : Finset G) (i : N) (g : G) :
    implements (rps pick D (T + 1) M') i g =
      eating pick M' i g + ∑ k, (D (eating pick M')).w k *
        implements (rps pick D T (M' \ univ.biUnion ((D (eating pick M')).A k))) i g := by
  set d := D (eating pick M')
  have hd : IsBvNDecomp (eating pick M') d := hdec I pick hpick D hD M'
  simp only [implements, rps, List.map_map, Function.comp_def]
  rw [sum_hist_succ]
  have : ∀ k, ((rpsHist pick D T (M' \ univ.biUnion (d.A k))).map fun e' =>
      d.w k * e'.1 * toFrac (unionHist (d.A k :: e'.2)) i g).sum =
      d.w k * toFrac (d.A k) i g + d.w k *
        ((rpsHist pick D T (M' \ univ.biUnion (d.A k))).map fun e' =>
          e'.1 * toFrac (unionHist e'.2) i g).sum := by
    intro k
    have hs := (hist_basic I pick hpick D hD T (M' \ univ.biUnion (d.A k))).2
    rw [List.map_congr_left (g := fun e' => d.w k * e'.1 *
        (toFrac (d.A k) i g + toFrac (unionHist e'.2) i g))
      (fun e' he' => by rw [toFrac_cons I pick hpick D hD T M' k e' he' i g])]
    rw [list_aux, hs, mul_one]
  simp only [d] at this ⊢
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, hd.2.2.1 i g]

end Main

end RPSAux

open ExAnteExPost.RPS in
theorem solution {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]
    [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D)
    (T : ℕ) (M' : Finset G) (i : N) (g : G) :
    implements (rps pick D (T + 1) M') i g =
      eating pick M' i g + ∑ k, (D (eating pick M')).w k *
        implements (rps pick D T (M' \ Finset.univ.biUnion ((D (eating pick M')).A k))) i g :=
  RPSAux.implements_succ I pick hpick D hD T M' i g
