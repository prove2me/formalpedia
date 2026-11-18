-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:03:14.902832+00:00
-- url     : https://prove2.me/submissions/f549d505-ff0d-4e38-8caa-dd4c89bf3dc8

import Theorems.Thm_DistancePreserver934_Exact_lemma_17

set_option autoImplicit false
open Classical DistancePreserver934.Exact

private lemma vol_pos {V : Type} [Fintype V] (H : SimpleGraph V) (x : V)
    (r : ℝ) (hr : 0 ≤ r) : 0 < vol H x r := by
  apply Finset.card_pos.mpr
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, by simp, by simpa using hr⟩⟩

theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ)
      (Vs : Finset V),
      Sec5Context G H R n d l → Eq5 d l r → Eq6 H R Vs n d →
      ∃ Λ' : Finset (Sym2 V), Λ' ⊆ coreEdges H R Vs ∧
        ((coreEdges H R Vs).card : ℝ) / 2 ≤ (Λ'.card : ℝ) ∧ (n : ℝ) * d / 80 ≤ (Λ'.card : ℝ) ∧
        ∀ e ∈ Λ', IsGoodEdge H R Vs d r C e := by
  obtain ⟨C₀,hC₀,hconflict⟩ := DistancePreserver934.Exact.lemma_17
  refine ⟨2*C₀, by positivity, ?_⟩
  intro V inst G H R n d l r Vs hctx h5 h6
  classical
  have hv : 0 < Fintype.card V :=
    (Finset.card_pos.mpr h6.1).trans_le (Finset.card_le_univ _)
  have hn : 0 < (n : ℝ) := by exact_mod_cast hv.trans_le hctx.2.2.1
  have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℝ)<6) h5.1
  have hnd : 0 ≤ (n : ℝ)*d := (Nat.cast_nonneg (numEdges H)).trans hctx.2.2.2.1
  have hd : 0 < d := by have := (le_min_iff.mp h5.2).1; nlinarith
  let b := d * Real.sqrt r
  have hb : 0 < b := mul_pos hd (Real.sqrt_pos.mpr hr)
  let E := coreEdges H R Vs
  let F := E.filter (IsGoodEdge H R Vs d r (2*C₀))
  let B := E.filter (fun e => ¬ IsGoodEdge H R Vs d r (2*C₀) e)
  let w : Sym2 V → ℝ := fun e => ∑ x ∈ Vs, if x ∈ e then
      (lamStar H R Vs x (r/2) (essSet H R e) : ℝ) / vol H x r else 0
  have hw (e : Sym2 V) : 0 ≤ w e := by
    apply Finset.sum_nonneg
    intro x hx
    split_ifs <;> positivity
  have hsum : ∑ e ∈ E, w e = conflictSum H R Vs r := by
    dsimp [w, conflictSum, E]
    rw [Finset.sum_comm]
    simp only [Finset.sum_filter]
  have hbad : ∀ e ∈ B, 2*C₀/b ≤ w e := by
    intro e he
    obtain ⟨he,hbad⟩ := Finset.mem_filter.mp he
    simp only [IsGoodEdge, not_forall] at hbad
    obtain ⟨x,hxe,hbad⟩ := hbad
    have hxV : x ∈ Vs := (Finset.mem_filter.mp he).2 x hxe
    have hvp : 0 < (vol H x r : ℝ) := by exact_mod_cast vol_pos H x r hr.le
    have hsmall : 2*C₀/b < (lamStar H R Vs x (r/2) (essSet H R e) : ℝ) / vol H x r := by
      apply (div_lt_div_iff₀ hb hvp).mpr
      exact (div_lt_iff₀ hb).mp (lt_of_not_ge hbad)
    have hle : (lamStar H R Vs x (r/2) (essSet H R e) : ℝ) / vol H x r ≤ w e := by
      have h := Finset.single_le_sum (s := Vs)
        (f := fun y => if y ∈ e then (lamStar H R Vs y (r/2) (essSet H R e) : ℝ) / vol H y r else 0)
        (fun y _ => by split_ifs <;> positivity) hxV
      simpa only [if_pos hxe] using h
    exact hsmall.le.trans hle
  have hbsum : (B.card : ℝ)*(2*C₀/b) ≤ ∑ e ∈ E, w e := by
    calc
      _ = ∑ _e ∈ B, 2*C₀/b := by simp
      _ ≤ ∑ e ∈ B, w e := Finset.sum_le_sum hbad
      _ ≤ ∑ e ∈ E, w e := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun e _ _ => hw e)
  have hupper : ∑ e ∈ E, w e ≤ C₀ * (E.card : ℝ) / b := by
    rw [hsum]
    exact hconflict V G H R n d l r Vs hctx h5 h6
  have hbcard : (B.card : ℝ) ≤ (E.card : ℝ)/2 := by
    have h := hbsum.trans hupper
    have heq : (B.card : ℝ)*(2*C₀/b) = ((B.card : ℝ)*(2*C₀))/b := by ring
    rw [heq] at h
    have h' := (div_le_div_iff_of_pos_right hb).mp h
    nlinarith
  have hcards : (F.card : ℝ) + (B.card : ℝ) = (E.card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := E)
      (p := IsGoodEdge H R Vs d r (2*C₀))
  refine ⟨F, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · change (E.card : ℝ)/2 ≤ (F.card : ℝ)
    linarith
  · have hm := h6.2.1
    change (n : ℝ)*d/40 ≤ (E.card : ℝ) at hm
    linarith
  · intro e he
    exact (Finset.mem_filter.mp he).2
