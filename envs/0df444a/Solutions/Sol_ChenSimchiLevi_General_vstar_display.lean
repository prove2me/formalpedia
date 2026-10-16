-- Prove2me | solution 1 for ChenSimchiLevi.General.vstar_display
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T04:42:03.948504+00:00
-- url     : https://prove2.me/submissions/ad26576c-f606-4794-baf3-6314233511a7

import Mathlib
import Definitions.Def_ChenSimchiLevi_General_OrderEnvelope
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

open ChenSimchiLevi.General Filter in
theorem solution (k : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k)
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
            simp only at this
            rw [← hxeq] at this
            have hm : max l (1 - l) ≤ 1 := max_le hl1 (by linarith)
            have h1l : 0 ≤ 1 - l := by linarith
            nlinarith [mul_le_mul_of_nonneg_right hm hk, mul_le_mul_of_nonneg_left (hS y) h1l]
    · exact hge_G x
