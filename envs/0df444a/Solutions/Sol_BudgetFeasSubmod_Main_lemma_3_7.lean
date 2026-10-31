-- Prove2me | solution 1 for BudgetFeasSubmod.Main.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:53:51.759638+00:00
-- url     : https://prove2.me/submissions/727807ba-6080-4075-8a7e-bc91f53fe663

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

open BudgetFeasSubmod.Main Finset NonmonotoneSubmod.Shared

namespace BFS37

variable {A : Type} [Fintype A] [DecidableEq A]

/-- `2 |S| ≤ |U|` when `f` injects `S` into `U` and moves every point of `S` out of `S`. -/
lemma double_card {α : Type} [DecidableEq α] (S U : Finset α) (f : α → α) (hS : S ⊆ U)
    (hf : ∀ x ∈ S, f x ∈ U) (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y)
    (hout : ∀ x ∈ S, f x ∉ S) : 2 * S.card ≤ U.card := by
  have hdisj : Disjoint S (S.image f) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
    exact hout y hy hx
  have himg : (S.image f).card = S.card := Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)
  have hsub : S ∪ S.image f ⊆ U := Finset.union_subset hS (by
    intro y hy; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy; exact hf x hx)
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, himg] at this
  omega

/-- flip the `P`-part of `X`, keep its `Q`-part -/
def flip (P Q X : Finset A) : Finset A := (X ∩ Q) ∪ (P \ X)

lemma flip_props (P Q T X : Finset A) (hPQ : Disjoint P Q) (hT : P ∪ Q = T) (hX : X ⊆ T) :
    flip P Q X ⊆ T ∧ flip P Q X ∩ Q = X ∩ Q ∧ flip P Q X ∩ P = P \ (X ∩ P) ∧
      flip P Q (flip P Q X) = X := by
  have hPQ' := Finset.disjoint_left.mp hPQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    unfold flip at ha
    rcases Finset.mem_union.mp ha with h | h
    · rw [← hT]; exact Finset.mem_union_right _ (Finset.mem_inter.mp h).2
    · rw [← hT]; exact Finset.mem_union_left _ (Finset.mem_sdiff.mp h).1
  · ext a; unfold flip
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨h | h, hq⟩
      · exact h
      · exact absurd hq (hPQ' h.1)
    · rintro ⟨hx, hq⟩; exact ⟨Or.inl ⟨hx, hq⟩, hq⟩
  · ext a; unfold flip
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨h | h, hp⟩
      · exact absurd h.2 (hPQ' hp)
      · exact ⟨hp, fun hh => h.2 hh.1⟩
    · rintro ⟨hp, hn⟩; exact ⟨Or.inr ⟨hp, fun hx => hn ⟨hx, hp⟩⟩, hp⟩
  · ext a; unfold flip
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    have hXT := @hX a
    rw [← hT, Finset.mem_union] at hXT
    constructor
    · rintro (⟨h | h, hq⟩ | ⟨hp, hn⟩)
      · exact h.1
      · exact absurd hq (hPQ' h.1)
      · by_contra hx; exact hn (Or.inr ⟨hp, hx⟩)
    · intro hx
      rcases hXT hx with hp | hq
      · right; refine ⟨hp, ?_⟩
        rintro (⟨_, hq⟩ | ⟨_, hn⟩)
        · exact hPQ' hp hq
        · exact hn hx
      · left; exact ⟨Or.inl ⟨hx, hq⟩, hq⟩

end BFS37

open BFS37 in
theorem solution {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ) (T : Finset A)
    (k : ℕ) (hv : IsValuation v) (hk : 0 < k) (hT : ∀ i ∈ T, (k : ℝ) * v {i} ≤ v T) :
    2 ^ T.card ≤ 2 * (T.powerset.filter (fun T₁ =>
      ((k : ℝ) - 1) / (4 * k) * v T ≤ v T₁ ∧ ((k : ℝ) - 1) / (4 * k) * v T ≤ v (T \ T₁))).card := by
  obtain ⟨hv0, hvnn, hsub⟩ := hv
  set W := v T with hW
  set α := ((k : ℝ) - 1) / (4 * k) with hα
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hW0 : 0 ≤ W := hvnn T
  have hα0 : 0 ≤ α := by rw [hα]; apply div_nonneg <;> linarith
  -- the monotone subadditive lower envelope of v on subsets of T
  have hne : ∀ S : Finset A, (T.powerset.filter (fun R => S ∩ T ⊆ R)).Nonempty := fun S =>
    ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self T, Finset.inter_subset_right⟩⟩
  let w : Finset A → ℝ := fun S => (T.powerset.filter (fun R => S ∩ T ⊆ R)).inf' (hne S) v
  have w_le : ∀ S ⊆ T, w S ≤ v S := by
    intro S hS
    apply Finset.inf'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, Finset.inter_subset_left⟩
  have w_mono : ∀ S S' : Finset A, S ⊆ S' → w S ≤ w S' := by
    intro S S' h
    apply Finset.le_inf'
    intro R hR
    apply Finset.inf'_le
    rw [Finset.mem_filter] at hR ⊢
    exact ⟨hR.1, le_trans (Finset.inter_subset_inter_right h) hR.2⟩
  have w_sub : ∀ S S' : Finset A, w (S ∪ S') ≤ w S + w S' := by
    intro S S'
    obtain ⟨R, hR, hRe⟩ := Finset.exists_mem_eq_inf' (hne S) v
    obtain ⟨R', hR', hRe'⟩ := Finset.exists_mem_eq_inf' (hne S') v
    rw [Finset.mem_filter, Finset.mem_powerset] at hR hR'
    have h1 : w (S ∪ S') ≤ v (R ∪ R') := by
      apply Finset.inf'_le
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.union_subset hR.1 hR'.1, ?_⟩
      rw [Finset.union_inter_distrib_right]
      exact Finset.union_subset_union hR.2 hR'.2
    have h2 := hsub R R'
    have h3 := hvnn (R ∩ R')
    have e1 : w S = v R := hRe
    have e2 : w S' = v R' := hRe'
    linarith
  have wT : w T = W := by
    apply le_antisymm (w_le T (le_refl T))
    apply Finset.le_inf'
    intro R hR
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.inter_self] at hR
    rw [Finset.Subset.antisymm hR.1 hR.2]
  have w_nonneg : ∀ S, 0 ≤ w S := by
    intro S
    apply Finset.le_inf'
    intro R _; exact hvnn R
  -- a deterministic split T = L ∪ R with both halves worth at least 2αW
  set θ := 2 * α * W with hθ
  have hθW : θ ≤ W := by
    rw [hθ, hα]
    have : 2 * (((k : ℝ) - 1) / (4 * k)) ≤ 1 := by
      rw [show 2 * (((k : ℝ) - 1) / (4 * k)) = ((k : ℝ) - 1) / (2 * k) by field_simp; ring]
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  set F := T.powerset.filter (fun L => θ ≤ w L) with hF
  have hTF : T ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_powerset_self T, by rw [wT]; exact hθW⟩
  obtain ⟨L, hLF, hLmin⟩ := Finset.exists_min_image F Finset.card ⟨T, hTF⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hLF
  set R := T \ L with hR
  have hwR : θ ≤ w R := by
    rcases Finset.eq_empty_or_nonempty L with hL0 | ⟨e, he⟩
    · have : θ ≤ 0 := by
        have := hLF.2; rw [hL0] at this
        have h0 := w_le ∅ (Finset.empty_subset _); rw [hv0] at h0; linarith
      exact le_trans this (w_nonneg R)
    · have hsmall : w (L.erase e) < θ := by
        by_contra hh
        push Not at hh
        have hmem : L.erase e ∈ F := Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (le_trans (Finset.erase_subset _ _) hLF.1), hh⟩
        have := hLmin _ hmem
        have := Finset.card_erase_lt_of_mem he
        omega
      have hTsplit : T = L.erase e ∪ ({e} ∪ R) := by
        ext a; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, hR,
          Finset.mem_sdiff]
        constructor
        · intro ha
          by_cases hae : a = e
          · right; left; exact hae
          · by_cases haL : a ∈ L
            · left; exact ⟨hae, haL⟩
            · right; right; exact ⟨ha, haL⟩
        · rintro (⟨_, h⟩ | rfl | ⟨h, _⟩)
          · exact hLF.1 h
          · exact hLF.1 he
          · exact h
      have h1 : W ≤ w (L.erase e) + (w {e} + w R) := by
        rw [← wT, hTsplit]
        exact le_trans (w_sub _ _) (by linarith [w_sub {e} R])
      have h2 : w {e} ≤ v {e} := w_le {e} (Finset.singleton_subset_iff.mpr (hLF.1 he))
      have h3 := hT e (hLF.1 he)
      have h4 : (k : ℝ) * w {e} ≤ W := le_trans (mul_le_mul_of_nonneg_left h2 (by linarith)) h3
      -- W - θ - W/k ≥ θ
      have h5 : θ * k ≤ (W - θ) * k - W := by
        rw [hθ, hα]; field_simp; ring_nf; nlinarith
      nlinarith
  have hwL : θ ≤ w L := hLF.2
  have hLR : Disjoint L R := Finset.disjoint_sdiff
  have hLRT : L ∪ R = T := Finset.union_sdiff_of_subset hLF.1
  have hRLT : R ∪ L = T := by rw [Finset.union_comm]; exact hLRT
  -- splitting a half: one of the two pieces keeps αW
  have split : ∀ P : Finset A, θ ≤ w P → ∀ X : Finset A, α * W ≤ w (X ∩ P) ∨ α * W ≤ w (P \ (X ∩ P)) := by
    intro P hP X
    have : w P ≤ w (X ∩ P) + w (P \ (X ∩ P)) := by
      have e : P = (X ∩ P) ∪ (P \ (X ∩ P)) := (Finset.union_sdiff_of_subset Finset.inter_subset_right).symm
      calc w P = w ((X ∩ P) ∪ (P \ (X ∩ P))) := by rw [← e]
        _ ≤ _ := w_sub _ _
    by_contra hh; push Not at hh
    have : θ = α * W + α * W := by rw [hθ]; ring
    linarith
  -- bad events
  set B1 := T.powerset.filter (fun X => w (X ∩ L) < α * W ∧ w (X ∩ R) < α * W) with hB1
  set B2 := T.powerset.filter (fun X => w ((T \ X) ∩ L) < α * W ∧ w ((T \ X) ∩ R) < α * W)
    with hB2
  set N := T.powerset.filter (fun X => w (X ∩ R) < α * W) with hN
  -- 2|B1| ≤ |N|  (flip the L-part)
  have hB1N : 2 * B1.card ≤ N.card := by
    apply double_card B1 N (flip L R)
    · intro X hX; rw [hB1, Finset.mem_filter] at hX; rw [hN, Finset.mem_filter]; exact ⟨hX.1, hX.2.2⟩
    · intro X hX
      rw [hB1, Finset.mem_filter, Finset.mem_powerset] at hX
      obtain ⟨p1, p2, -, -⟩ := flip_props L R T X hLR hLRT hX.1
      rw [hN, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨p1, by rw [p2]; exact hX.2.2⟩
    · intro X hX Y hY h
      rw [hB1, Finset.mem_filter, Finset.mem_powerset] at hX hY
      rw [← (flip_props L R T X hLR hLRT hX.1).2.2.2, ← (flip_props L R T Y hLR hLRT hY.1).2.2.2, h]
    · intro X hX hX'
      rw [hB1, Finset.mem_filter, Finset.mem_powerset] at hX hX'
      obtain ⟨-, -, p3, -⟩ := flip_props L R T X hLR hLRT hX.1
      rw [p3] at hX'
      rcases split L hwL X with h | h
      · linarith [hX.2.1]
      · linarith [hX'.2.1]
  -- 2|N| ≤ 2^|T|  (flip the R-part)
  have hNP : 2 * N.card ≤ T.powerset.card := by
    apply double_card N T.powerset (flip R L)
    · exact Finset.filter_subset _ _
    · intro X hX
      rw [hN, Finset.mem_filter, Finset.mem_powerset] at hX
      exact Finset.mem_powerset.mpr (flip_props R L T X hLR.symm hRLT hX.1).1
    · intro X hX Y hY h
      rw [hN, Finset.mem_filter, Finset.mem_powerset] at hX hY
      rw [← (flip_props R L T X hLR.symm hRLT hX.1).2.2.2,
        ← (flip_props R L T Y hLR.symm hRLT hY.1).2.2.2, h]
    · intro X hX hX'
      rw [hN, Finset.mem_filter, Finset.mem_powerset] at hX hX'
      obtain ⟨-, -, p3, -⟩ := flip_props R L T X hLR.symm hRLT hX.1
      rw [p3] at hX'
      rcases split R hwR X with h | h
      · linarith [hX.2]
      · linarith [hX'.2]
  -- |B2| ≤ |B1|  (complement)
  have hB21 : B2.card ≤ B1.card := by
    apply Finset.card_le_card_of_injOn (fun X => T \ X)
    · intro X hX
      rw [Finset.mem_coe, hB2, Finset.mem_filter] at hX
      rw [Finset.mem_coe, hB1, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, hX.2⟩
    · intro X hX Y hY h
      rw [Finset.mem_coe, hB2, Finset.mem_filter, Finset.mem_powerset] at hX hY
      simp only at h
      rw [← Finset.sdiff_sdiff_eq_self hX.1, ← Finset.sdiff_sdiff_eq_self hY.1, h]
  -- good outside B1 ∪ B2
  set G := T.powerset.filter (fun T₁ =>
      ((k : ℝ) - 1) / (4 * k) * v T ≤ v T₁ ∧ ((k : ℝ) - 1) / (4 * k) * v T ≤ v (T \ T₁)) with hG
  have hcover : T.powerset ⊆ G ∪ (B1 ∪ B2) := by
    intro X hX
    have hXT := Finset.mem_powerset.mp hX
    by_cases h1 : X ∈ B1
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h1)
    by_cases h2 : X ∈ B2
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h2)
    apply Finset.mem_union_left
    rw [hB1, Finset.mem_filter] at h1
    rw [hB2, Finset.mem_filter] at h2
    have hgood : ∀ Y ⊆ T, ¬ (w (Y ∩ L) < α * W ∧ w (Y ∩ R) < α * W) → α * W ≤ v Y := by
      intro Y hY hn
      have hvY : w Y ≤ v Y := w_le Y hY
      by_cases hl : w (Y ∩ L) < α * W
      · have hr : α * W ≤ w (Y ∩ R) := by by_contra hh; push Not at hh; exact hn ⟨hl, hh⟩
        linarith [w_mono (Y ∩ R) Y Finset.inter_subset_left]
      · push Not at hl
        linarith [w_mono (Y ∩ L) Y Finset.inter_subset_left]
    rw [hG, Finset.mem_filter]
    refine ⟨hX, hgood X hXT (fun h => h1 ⟨hX, h⟩), hgood (T \ X) Finset.sdiff_subset
      (fun h => h2 ⟨hX, h⟩)⟩
  have hc := Finset.card_le_card hcover
  have hc2 := le_trans hc (Finset.card_union_le _ _)
  have hc3 := Finset.card_union_le B1 B2
  rw [Finset.card_powerset] at hc hNP hc2
  omega
