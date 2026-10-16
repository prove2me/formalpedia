-- Prove2me | solution 1 for ChenSimchiLevi.General.v_sym_concave
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T04:31:40.595261+00:00
-- url     : https://prove2.me/submissions/50a76557-7633-449d-b173-f98834a4d537

import Mathlib
import Definitions.Def_ChenSimchiLevi_General_OrderEnvelope
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

open ChenSimchiLevi.General Filter in
theorem vstar_display_aux (k : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k)
    (hGcont : Continuous G) (hGright : Tendsto G atTop atBot)
    (hGleft : Tendsto G atBot atBot)
    (hGsym : SymKConvex k (fun y => -G y))
    (S : ℝ) (hS : ∀ y, G y ≤ G S) :
    (∀ x, orderEnvelope k G x =
      if x ∈ {y | y ≤ S ∧ G y ≤ G S - k} then -k + G S else G x) ∧
    (∀ x, G x ≤ orderEnvelope k G x) ∧
    (∀ x ≤ S, -k + G S ≤ orderEnvelope k G x) := by
  have hδ0 : ∀ x : ℝ, δ (x - x) = 0 := fun x => by simp [δ]
  have hδ1 : ∀ x y : ℝ, x < y → δ (y - x) = 1 := fun x y h => by
    simp [δ, h]
  -- upper bound for elements
  have hub : ∀ x y : ℝ, x ≤ y → -k * δ (y - x) + G y ≤ G S := by
    intro x y _
    have h0 : 0 ≤ δ (y - x) := by unfold δ; split_ifs <;> norm_num
    nlinarith [hS y]
  have hbdd : ∀ x : ℝ, BddAbove ((fun y => -k * δ (y - x) + G y) '' Set.Ici x) := by
    intro x
    exact ⟨G S, by rintro _ ⟨y, hy, rfl⟩; exact hub x y hy⟩
  have hge_G : ∀ x, G x ≤ orderEnvelope k G x := by
    intro x
    apply le_csSup (hbdd x)
    exact ⟨x, Set.mem_Ici.mpr le_rfl, by show -k * δ (x - x) + G x = G x; rw [hδ0]; ring⟩
  have hge_S : ∀ x ≤ S, -k + G S ≤ orderEnvelope k G x := by
    intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · rw [h]
      have := hge_G S
      linarith
    · apply le_csSup (hbdd x)
      refine ⟨S, Set.mem_Ici.mpr hx, ?_⟩
      simp [hδ1 x S h]
  refine ⟨?_, hge_G, hge_S⟩
  intro x
  by_cases hx : x ∈ {y | y ≤ S ∧ G y ≤ G S - k}
  · rw [if_pos hx]
    have hxS : x ≤ S := hx.1
    have hGx : G x ≤ G S - k := hx.2
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, x, Set.mem_Ici.mpr le_rfl, rfl⟩
      · rintro _ ⟨y, hy, rfl⟩
        dsimp only
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with h | h
        · rw [← h, hδ0]; linarith
        · rw [hδ1 x y h]; linarith [hS y]
    · exact hge_S x hxS
  · rw [if_neg hx]
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, x, Set.mem_Ici.mpr le_rfl, rfl⟩
      · rintro _ ⟨y, hy, rfl⟩
        dsimp only
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with h | h
        · rw [← h, hδ0]; linarith
        · rw [hδ1 x y h]
          -- need G y - k ≤ G x
          have hcase : G S - k < G x ∨ S < x := by
            by_contra hcon
            push_neg at hcon
            exact hx ⟨hcon.2, hcon.1⟩
          rcases hcase with hc | hc
          · linarith [hS y]
          · -- S < x < y: sym-k-concavity of G
            have hxy : x < y := h
            have hSy : 0 < y - S := by linarith
            set l : ℝ := (x - S) / (y - S) with hl
            have hl0 : 0 ≤ l := div_nonneg (by linarith) hSy.le
            have hl1 : l ≤ 1 := by rw [hl, div_le_one hSy]; linarith
            have hxeq : x = (1 - l) * S + l * y := by
              rw [hl]; field_simp; ring
            have := hGsym S y l ⟨hl0, hl1⟩
            try simp only at this
            rw [← hxeq] at this
            have hm : max l (1 - l) ≤ 1 := max_le hl1 (by linarith)
            have h1l : 0 ≤ 1 - l := by linarith
            nlinarith [mul_le_mul_of_nonneg_right hm hk, mul_le_mul_of_nonneg_left (hS y) h1l]
    · exact hge_G x

open ChenSimchiLevi.General Filter in
theorem solution (k : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k)
    (hGcont : Continuous G) (hGright : Tendsto G atTop atBot)
    (hGleft : Tendsto G atBot atBot)
    (hGsym : SymKConvex k (fun y => -G y)) (c : ℝ) :
    SymKConvex k (fun x => -(c * x + orderEnvelope k G x)) := by
  -- a global maximizer
  have hco : Tendsto (fun y => -G y) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact (tendsto_neg_atBot_atTop.comp hGleft).sup (tendsto_neg_atBot_atTop.comp hGright)
  obtain ⟨S, hS'⟩ := (hGcont.neg).exists_forall_le hco
  have hS : ∀ y, G y ≤ G S := fun y => by simpa using hS' y
  obtain ⟨hform, hge, hflat⟩ := vstar_display_aux k G hk hGcont hGright hGleft hGsym S hS
  set u := orderEnvelope k G with hu
  have hdich : ∀ x, u x = G x ∨ (x ≤ S ∧ u x = G S - k) := by
    intro x
    rw [hform x]
    by_cases hx : x ∈ {y | y ≤ S ∧ G y ≤ G S - k}
    · rw [if_pos hx]; right; exact ⟨hx.1, by ring⟩
    · rw [if_neg hx]; left; rfl
  have hle : ∀ x, u x ≤ G S := by
    intro x
    rcases hdich x with h | h
    · rw [h]; exact hS x
    · rw [h.2]; linarith
  -- the mixed case
  have mixed : ∀ x0 x1 l : ℝ, x0 ≤ S → u x0 = G S - k → u x1 = G x1 → 0 ≤ l → l ≤ 1 →
      (1 - l) * u x0 + l * u x1 - max l (1 - l) * k ≤ u ((1 - l) * x0 + l * x1) := by
    intro x0 x1 l hx0 hu0 hu1 hl0 hl1
    have hL : l ≤ max l (1 - l) := le_max_left _ _
    have hL1 : max l (1 - l) ≤ 1 := max_le hl1 (by linarith)
    have hL0 : 0 ≤ max l (1 - l) := le_trans hl0 hL
    set xl := (1 - l) * x0 + l * x1 with hxl
    by_cases hxS : xl ≤ S
    · have h1 := hflat xl hxS
      have h2 := hS x1
      rw [hu0, hu1]
      nlinarith [mul_le_mul_of_nonneg_right hL hk, mul_le_mul_of_nonneg_left h2 hl0]
    · push_neg at hxS
      have hx1 : S < x1 := by
        by_contra hcon
        push_neg at hcon
        have : xl ≤ S := by
          rw [hxl]; nlinarith
        linarith
      have hSy : 0 < x1 - S := by linarith
      set m : ℝ := (xl - S) / (x1 - S) with hm
      have hm0 : 0 ≤ m := div_nonneg (by linarith) hSy.le
      have hxl_le : xl ≤ x1 := by rw [hxl]; nlinarith
      have hm1 : m ≤ 1 := by rw [hm, div_le_one hSy]; linarith
      have hmeq : xl = (1 - m) * S + m * x1 := by
        rw [hm]; field_simp; ring
      have hml : m ≤ l := by
        rw [hm, div_le_iff₀ hSy, hxl]
        nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hx0)]
      have hsym := hGsym S x1 m ⟨hm0, hm1⟩
      try simp only at hsym
      rw [← hmeq] at hsym
      have hM1 : max m (1 - m) ≤ 1 := max_le hm1 (by linarith)
      have hGxl : G xl ≤ u xl := hge xl
      have h2 := hS x1
      rw [hu0, hu1]
      have e1 : 0 ≤ (l - m) * (G S - G x1) := mul_nonneg (by linarith) (by linarith)
      have e2 : 0 ≤ k * ((1 - l) + max l (1 - l) - max m (1 - m)) :=
        mul_nonneg hk (by linarith)
      nlinarith [e1, e2]
  intro x0 x1 l hl
  obtain ⟨hl0, hl1⟩ := hl
  try simp only
  have hkey : (1 - l) * u x0 + l * u x1 - max l (1 - l) * k ≤ u ((1 - l) * x0 + l * x1) := by
    rcases hdich x0 with h0 | h0 <;> rcases hdich x1 with h1 | h1
    · have := hGsym x0 x1 l ⟨hl0, hl1⟩
      try simp only at this
      have := hge ((1 - l) * x0 + l * x1)
      rw [h0, h1]
      nlinarith
    · -- x0 in G-region, x1 flat
      have := mixed x1 x0 (1 - l) h1.1 h1.2 h0 (by linarith) (by linarith)
      have e : (1 - (1 - l)) * x1 + (1 - l) * x0 = (1 - l) * x0 + l * x1 := by ring
      have e2 : max (1 - l) (1 - (1 - l)) = max l (1 - l) := by rw [sub_sub_cancel, max_comm]
      rw [e, e2] at this
      linarith
    · exact mixed x0 x1 l h0.1 h0.2 h1 hl0 hl1
    · have hx1S := h1.1
      have hxlS : (1 - l) * x0 + l * x1 ≤ S := by nlinarith [h0.1]
      have := hflat _ hxlS
      rw [h0.2, h1.2]
      have : 0 ≤ max l (1 - l) * k := mul_nonneg (le_trans hl0 (le_max_left _ _)) hk
      nlinarith
  have e : c * ((1 - l) * x0 + l * x1) = (1 - l) * (c * x0) + l * (c * x1) := by ring
  nlinarith [hkey, e]
