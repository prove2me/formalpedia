-- Prove2me | solution 1 for BudgetFeasSubmod.Main.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:51:36.417168+00:00
-- url     : https://prove2.me/submissions/c7abe5ad-c719-4a2d-a4b6-288c591894a6

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model
import Theorems.Thm_BudgetFeasSubmod_Main_lemma_3_6
import Theorems.Thm_BudgetFeasSubmod_Main_lemma_3_7

open BudgetFeasSubmod.Main Finset

namespace BFS38

lemma opt_ge {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ) (c : A → ℝ) (B : ℝ)
    (X T : Finset A) (hT : T ⊆ X) (hc : ∑ i ∈ T, c i ≤ B) : v T ≤ opt v c B X := by
  have hmem : T ∈ X.powerset.filter (fun T => ∑ i ∈ T, c i ≤ B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT, hc⟩
  unfold opt
  rw [dif_pos ⟨T, hmem⟩]
  exact Finset.le_sup' v hmem

lemma opt_attained {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ) (c : A → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (X : Finset A) :
    ∃ T ⊆ X, ∑ i ∈ T, c i ≤ B ∧ v T = opt v c B X := by
  have hne : (X.powerset.filter (fun T => ∑ i ∈ T, c i ≤ B)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset X, by simpa using hB⟩⟩
  obtain ⟨T, hT, hTeq⟩ := Finset.exists_mem_eq_sup' hne v
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  refine ⟨T, hT.1, hT.2, ?_⟩
  unfold opt
  rw [dif_pos hne, hTeq]

/-- counting: a property of `X ∩ T` holding for at least half the subsets of `T` holds for at
least half the subsets of the whole ground set -/
lemma count_lift {A : Type} [Fintype A] [DecidableEq A] (T : Finset A) (P : Finset A → Prop)
    [DecidablePred P] (h : 2 ^ T.card ≤ 2 * (T.powerset.filter P).card) :
    2 ^ Fintype.card A ≤ 2 * (univ.powerset.filter (fun X => P (X ∩ T))).card := by
  set G := T.powerset.filter P
  set R := (univ \ T).powerset
  have hinj : (G ×ˢ R).card ≤ (univ.powerset.filter (fun X => P (X ∩ T))).card := by
    apply Finset.card_le_card_of_injOn (fun p => p.1 ∪ p.2)
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_product] at hp
      have h1 := Finset.mem_filter.mp hp.1
      have hY := Finset.mem_powerset.mp h1.1
      have hZ := Finset.mem_powerset.mp hp.2
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      have : (p.1 ∪ p.2) ∩ T = p.1 := by
        ext a; constructor
        · intro ha
          rcases Finset.mem_union.mp (Finset.mem_inter.mp ha).1 with h | h
          · exact h
          · exact absurd (Finset.mem_inter.mp ha).2 (Finset.mem_sdiff.mp (hZ h)).2
        · intro ha; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ ha, hY ha⟩
      rw [this]; exact h1.2
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_product] at hp hq
      have hY1 := Finset.mem_powerset.mp (Finset.mem_filter.mp hp.1).1
      have hY2 := Finset.mem_powerset.mp (Finset.mem_filter.mp hq.1).1
      have hZ1 := Finset.mem_powerset.mp hp.2
      have hZ2 := Finset.mem_powerset.mp hq.2
      simp only at hpq
      have key : ∀ (Y Z : Finset A), Y ⊆ T → Z ⊆ univ \ T → (Y ∪ Z) ∩ T = Y ∧ (Y ∪ Z) \ T = Z := by
        intro Y Z hY hZ
        constructor
        · ext a; constructor
          · intro ha
            rcases Finset.mem_union.mp (Finset.mem_inter.mp ha).1 with h | h
            · exact h
            · exact absurd (Finset.mem_inter.mp ha).2 (Finset.mem_sdiff.mp (hZ h)).2
          · intro ha; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ ha, hY ha⟩
        · ext a; constructor
          · intro ha
            rcases Finset.mem_union.mp (Finset.mem_sdiff.mp ha).1 with h | h
            · exact absurd (hY h) (Finset.mem_sdiff.mp ha).2
            · exact h
          · intro ha
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ ha, (Finset.mem_sdiff.mp (hZ ha)).2⟩
      have e1 := key p.1 p.2 hY1 hZ1
      have e2 := key q.1 q.2 hY2 hZ2
      rw [hpq] at e1
      exact Prod.ext (e1.1.symm.trans e2.1) (e1.2.symm.trans e2.2)
  rw [Finset.card_product, Finset.card_powerset, Finset.card_univ_diff] at hinj
  have hle : T.card ≤ Fintype.card A := Finset.card_le_univ T
  have hsplit : 2 ^ Fintype.card A = 2 ^ T.card * 2 ^ (Fintype.card A - T.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [hsplit]
  calc 2 ^ T.card * 2 ^ (Fintype.card A - T.card)
      ≤ 2 * G.card * 2 ^ (Fintype.card A - T.card) := Nat.mul_le_mul_right _ h
    _ = 2 * (G.card * 2 ^ (Fintype.card A - T.card)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hinj

end BFS38

open BFS38 in
theorem solution {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] (v : Finset A → ℝ)
    (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (β B : ℝ) (c : A → ℝ) (k : ℕ)
    (hv : IsValuation v) (h1 : IsKnapsackEApprox v B alg1) (h2 : IsUnconstrainedTwoApprox v alg2)
    (htb : IsArgmaxRule v tb) (hβ : 0 < β) (hB : 0 < B) (hc : InDomain B c) (hk : 0 < k)
    (hopt : ∀ i : A, (k : ℝ) * v {i} < opt v c B univ) :
    2 ^ Fintype.card A ≤ 2 * (univ.powerset.filter (fun A₁ : Finset A =>
      min ((⌊((k : ℝ) - 1) / (4 * Real.exp 1 * β)⌋₊ : ℝ) * ((k : ℝ) - 1) /
            (Real.exp 1 * ((⌊((k : ℝ) - 1) / (4 * Real.exp 1 * β)⌋₊ : ℝ) + 1)))
          ((β * ((k : ℝ) - 1) - 8 * k) / 6) * (1 / (4 * β * k)) * opt v c B univ ≤
        v (sampleThenGreedy v alg1 alg2 tb β B A₁ c))).card := by
  have hv0 : ∀ S, 0 ≤ v S := hv.2.1
  set O := opt v c B univ with hO
  have hO0 : 0 ≤ O := by
    obtain ⟨i⟩ := (inferInstance : Nonempty A)
    have := hopt i; have := hv0 {i}; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; nlinarith
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  set ℓ := ⌊((k : ℝ) - 1) / (4 * Real.exp 1 * β)⌋₊ with hℓ
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set bound := min ((ℓ : ℝ) * ((k : ℝ) - 1) / (Real.exp 1 * ((ℓ : ℝ) + 1)))
          ((β * ((k : ℝ) - 1) - 8 * k) / 6) * (1 / (4 * β * k)) * O with hbound
  have ht0 : 0 ≤ 1 / (4 * β * k) * O := by positivity
  by_cases hℓ0 : ℓ = 0
  · -- the bound is non-positive: every halving qualifies
    have hb : bound ≤ 0 := by
      rw [hbound, hℓ0, mul_assoc]
      apply mul_nonpos_of_nonpos_of_nonneg _ ht0
      apply le_trans (min_le_left _ _)
      simp
    rw [Finset.filter_true_of_mem (fun A₁ _ => le_trans hb (hv0 _)), Finset.card_powerset,
      Finset.card_univ]
    omega
  · have hℓpos : 0 < ℓ := Nat.pos_of_ne_zero hℓ0
    have hℓR : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓpos
    have hℓle : (ℓ : ℝ) ≤ ((k : ℝ) - 1) / (4 * Real.exp 1 * β) := by
      apply Nat.floor_le
      by_contra hneg
      push Not at hneg
      have : ℓ = 0 := Nat.floor_eq_zero.mpr (lt_of_lt_of_le hneg zero_le_one)
      exact hℓ0 this
    have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (0:ℝ) < ((k : ℝ) - 1) / (4 * Real.exp 1 * β) := lt_of_lt_of_le hℓR hℓle
      have h4 : 0 < 4 * Real.exp 1 * β := by positivity
      have := (div_pos_iff_of_pos_right h4).mp this
      linarith
    -- an optimal solution
    obtain ⟨C, -, hCc, hCv⟩ := opt_attained v c B hB.le univ
    have hT : ∀ i ∈ C, (k : ℝ) * v {i} ≤ v C := fun i _ => by rw [hCv]; exact le_of_lt (hopt i)
    have h37 := lemma_3_7 v C k hv hk hT
    set α := ((k : ℝ) - 1) / (4 * k) with hα
    have hlift := count_lift C (fun T₁ => α * v C ≤ v T₁ ∧ α * v C ≤ v (C \ T₁)) h37
    refine le_trans hlift (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    intro A₁ hA₁
    rw [Finset.mem_filter] at hA₁ ⊢
    refine ⟨hA₁.1, ?_⟩
    obtain ⟨hgood1, hgood2⟩ := hA₁.2
    have hCA : C \ (A₁ ∩ C) = C \ A₁ := by
      ext a; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [hCA] at hgood2
    rw [hCv] at hgood1 hgood2
    have hcsub : ∀ T ⊆ C, ∑ i ∈ T, c i ≤ B := fun T hTC =>
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hTC (fun i _ _ => (hc i).1)) hCc
    -- the estimate x
    set x := v (alg1 A₁ c) with hx
    obtain ⟨ha1, ha2, ha3⟩ := h1 A₁ c hc
    have hopt1 : α * O ≤ opt v c B A₁ :=
      le_trans hgood1 (opt_ge v c B A₁ _ Finset.inter_subset_left (hcsub _ Finset.inter_subset_right))
    have hxlow : α * O ≤ Real.exp 1 * x := le_trans hopt1 ha3
    have hxup : x ≤ O := opt_ge v c B univ _ (Finset.subset_univ _) ha2
    have hopt2 : α * O ≤ opt v c B (univ \ A₁) :=
      le_trans hgood2 (opt_ge v c B _ _ (Finset.sdiff_subset_sdiff (Finset.subset_univ _)
        (le_refl _)) (hcsub _ Finset.sdiff_subset))
    have hαdef : α * (4 * k) = (k : ℝ) - 1 := by rw [hα]; field_simp
    -- no agent is too valuable relative to x
    have hmax : ∀ i ∈ univ \ A₁, v {i} < x / ((ℓ : ℝ) * β) := by
      intro i _
      rw [lt_div_iff₀ (by positivity)]
      have h1' := hopt i
      -- ℓ β ≤ (k-1)/(4e)
      have hlb : (ℓ : ℝ) * β ≤ ((k : ℝ) - 1) / (4 * Real.exp 1) := by
        have := mul_le_mul_of_nonneg_right hℓle hβ.le
        rw [show ((k : ℝ) - 1) / (4 * Real.exp 1 * β) * β = ((k : ℝ) - 1) / (4 * Real.exp 1) by
          field_simp] at this
        exact this
      -- k x ≥ (k-1) O / (4e)
      have hkx : ((k : ℝ) - 1) / (4 * Real.exp 1) * O ≤ k * x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      have hvi := hv0 {i}
      have hq : 0 < ((k : ℝ) - 1) / (4 * Real.exp 1) :=
        lt_of_lt_of_le (by positivity) hlb
      have hm := mul_lt_mul_of_pos_right h1' hq
      have h3 : (k : ℝ) * (v {i} * (((k : ℝ) - 1) / (4 * Real.exp 1))) < k * x := by
        nlinarith
      have h4 : v {i} * (((k : ℝ) - 1) / (4 * Real.exp 1)) < x := lt_of_mul_lt_mul_left h3 hkR.le
      have h5 := mul_le_mul_of_nonneg_left hlb hvi
      linarith
    have h36 := lemma_3_6 v alg2 tb β B x (univ \ A₁) c ℓ hv h2 htb hβ hB hc hℓpos hmax
    have hstg : sampleThenGreedy v alg1 alg2 tb β B A₁ c =
        simGreedy v alg2 tb β B x (univ \ A₁) c := rfl
    rw [hstg]
    refine le_trans ?_ h36
    rw [hbound, mul_assoc, min_mul_of_nonneg _ _ ht0]
    apply min_le_min
    · -- ℓ (k-1) O / (e (ℓ+1) 4 β k) ≤ ℓ x / ((ℓ+1) β)
      have hx' : ((k : ℝ) - 1) * O ≤ 4 * k * Real.exp 1 * x := by nlinarith
      rw [show (ℓ : ℝ) * ((k : ℝ) - 1) / (Real.exp 1 * ((ℓ : ℝ) + 1)) * (1 / (4 * β * k) * O)
          = (ℓ : ℝ) * (((k : ℝ) - 1) * O) / ((Real.exp 1 * ((ℓ : ℝ) + 1)) * (4 * β * k)) by
            field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hx' (show (0:ℝ) ≤ ℓ * (((ℓ : ℝ) + 1) * β) by positivity)
      nlinarith
    · -- (β(k-1) - 8k)/6 · O/(4βk) ≤ (opt(D) - 2x/β)/6
      rw [show (β * ((k : ℝ) - 1) - 8 * k) / 6 * (1 / (4 * β * k) * O)
          = (α * O - 2 * O / β) / 6 by rw [hα]; field_simp; ring]
      have : 2 * x / β ≤ 2 * O / β := by
        apply div_le_div_of_nonneg_right _ hβ.le; linarith
      linarith
