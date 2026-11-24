-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.round_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:50.53267+00:00
-- url     : https://prove2.me/submissions/353ab264-4713-4d1d-b17b-9cdf02233360

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_keepPart_subset
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_sellPart_subset
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_keepPart_disjoint_sellPart
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_nonneg
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_priceSum_nonneg
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_effVal_le_add
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_effVal_le_of_price_le
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_le_nsmul_netSum
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_split
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_netSum_split
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_keepPart_le
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_minimal_bag

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
variable [DecidableEq G] (v : Fin n → G → ℝ) (p : G → ℝ) (t : Fin n → ℝ)
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) (ht : ∀ i, 0 ≤ t i) (hn : 0 < n)
    (R : Finset G) (s : ℝ) (hs : 0 ≤ s) (T : Finset (Fin n)) (hT : T.Nonempty)
    (hinv : ∀ k ∈ T, t k ≤ effSum (v k) p (t k) R + n * s) :
    ∃ i ∈ T, ∃ C D : Finset G, C ⊆ R ∧ D ⊆ R ∧ Disjoint C D ∧
      t i / n ≤ (∑ g ∈ C, v i g) + s + priceSum p D / n ∧
      (∀ k ∈ T, k ≠ i → effSum (v k) p (t k) (C ∪ D) - priceSum p D ≤ t k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Step 0: an agent that is already satisfied by the money she holds
  by_cases hsat : ∃ i ∈ T, t i / n ≤ s
  · obtain ⟨i, hi, hle⟩ := hsat
    refine ⟨i, hi, ∅, ∅, by simp, by simp, by simp, by simpa [priceSum] using hle, ?_⟩
    intro k hk hne
    simpa [effSum, priceSum] using ht k
  push_neg at hsat
  -- Step 1: a good that is more expensive than some active agent's target
  by_cases hexp : ∃ e ∈ R, ∃ i ∈ T, t i ≤ p e
  · obtain ⟨e, he, i, hi, hle⟩ := hexp
    refine ⟨i, hi, ∅, {e}, by simp, by simpa using he, by simp, ?_, ?_⟩
    · have hdiv : t i / n ≤ p e / n := by gcongr
      simpa [priceSum] using by linarith
    · intro k hk hne
      have hb := effVal_le_add (vi := v k) hp (ht k) e
      simp only [effSum, priceSum, Finset.empty_union, Finset.sum_singleton]
      linarith
  push_neg at hexp
  -- Step 2: a good that is valuable enough for some active agent
  by_cases hval : ∃ e ∈ R, ∃ i ∈ T, t i / n - s ≤ v i e
  · obtain ⟨e, he, i, hi, hle⟩ := hval
    refine ⟨i, hi, {e}, ∅, by simpa using he, by simp, by simp, ?_, ?_⟩
    · simp only [priceSum, Finset.sum_empty, Finset.sum_singleton, zero_div]
      linarith
    · intro k hk hne
      simp only [effSum, priceSum, Finset.union_empty, Finset.sum_singleton, Finset.sum_empty,
        sub_zero]
      exact effVal_le_of_price_le (hexp e he k hk).le
  push_neg at hval
  -- Step 3: bag filling
  have hRsat : ∀ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) R := by
    intro k hk
    have h1 := hinv k hk
    have h2 := effSum_le_nsmul_netSum (vi := v k) (p := p) (hv k) (ht k) hn R
    rw [sub_le_iff_le_add, div_le_iff₀ hn']
    nlinarith
  obtain ⟨k1, hk1⟩ := hT
  obtain ⟨B, hBR, hBsat, hBmin⟩ :=
    exists_minimal_bag v p t T s R ⟨k1, hk1, hRsat k1 hk1⟩
  obtain ⟨k0, hk0T, hk0⟩ := hBsat
  -- the bag is nonempty
  have hBne : B.Nonempty := by
    rcases Finset.eq_empty_or_nonempty B with hemp | hne
    · exfalso
      have h0 : netSum n (v k0) p (t k0) B = 0 := by simp [hemp, netSum]
      have := hsat k0 hk0T
      rw [h0] at hk0
      linarith
    · exact hne
  obtain ⟨e, heB⟩ := hBne
  have heR : e ∈ R := hBR heB
  -- the agents that the bag satisfies, and the winner among them
  classical
  obtain ⟨i, hiW, hmax⟩ :=
    Finset.exists_max_image (T.filter (fun k => t k / n - s ≤ netSum n (v k) p (t k) B))
      (fun k => priceSum p (sellPart (v k) p (t k) B))
      ⟨k0, Finset.mem_filter.mpr ⟨hk0T, hk0⟩⟩
  have hiT : i ∈ T := (Finset.mem_filter.mp hiW).1
  have hiB : t i / n - s ≤ netSum n (v i) p (t i) B := (Finset.mem_filter.mp hiW).2
  refine ⟨i, hiT, keepPart (v i) p (t i) B, sellPart (v i) p (t i) B,
    (keepPart_subset B).trans hBR, (sellPart_subset B).trans hBR,
    keepPart_disjoint_sellPart B, ?_, ?_⟩
  · -- the winner reaches her target
    have hsplit := netSum_split (n := n) (vi := v i) (p := p) (tk := t i) B
    have hkeep := effSum_keepPart_le (vi := v i) (p := p) (tk := t i) B
    rw [hsplit] at hiB
    linarith
  · -- every other active agent loses at most `t k` of potential
    intro k hk hne
    have hunion : keepPart (v i) p (t i) B ∪ sellPart (v i) p (t i) B = B :=
      Finset.filter_union_filter_not_eq _ _
    rw [hunion]
    set a : ℝ := effSum (v k) p (t k) (keepPart (v k) p (t k) B) with ha
    set b : ℝ := priceSum p (sellPart (v k) p (t k) B) with hb
    set d : ℝ := priceSum p (sellPart (v i) p (t i) B) with hd
    have hsplitE : effSum (v k) p (t k) B = a + b := effSum_split B
    have hsplitN : netSum n (v k) p (t k) B = a + b / n := netSum_split B
    have ha0 : 0 ≤ a := effSum_nonneg hp _
    have hb0 : 0 ≤ b := priceSum_nonneg hp _
    have hd0 : 0 ≤ d := priceSum_nonneg hp _
    rw [hsplitE]
    rcases le_or_gt b d with hbd | hbd
    · -- the winner generates at least as much money from the bag as `k` would
      -- so `k` is compensated; the bag is worth less than `2 tₖ/n` to her
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
        have hik : (i : ℕ) ≠ (k : ℕ) := fun h => hne (Fin.ext h).symm
        have h1 := i.isLt
        have h2 := k.isLt
        have : 2 ≤ n := by omega
        exact_mod_cast this
      have hremove : netSum n (v k) p (t k) B
          = netSum n (v k) p (t k) (B \ {e}) + netVal n (v k) p (t k) e := by
        unfold netSum
        rw [Finset.sum_sdiff_eq_sub (by simpa using heB)]
        simp
      have hlast : netVal n (v k) p (t k) e ≤ t k / n := by
        unfold netVal
        split
        · rename_i hkeep'
          have h1 := hval e heR k hk
          have h2 : min (v k e) (t k) ≤ v k e := min_le_left _ _
          have h3 : (0:ℝ) ≤ s := hs
          linarith
        · have := hexp e heR k hk
          gcongr
      have hprev := hBmin e heB k hk
      have hlt : netSum n (v k) p (t k) B < (t k / n - s) + t k / n := by
        rw [hremove]; linarith
      have hhalf : (t k / n) + (t k / n) ≤ t k := by
        rw [← add_div, div_le_iff₀ hn']
        nlinarith [ht k]
      have hbn : 0 ≤ b / n := by positivity
      linarith
    · -- the winner generates less money, so `k` did not qualify for the bag
      have hkW : k ∉ T.filter (fun k => t k / n - s ≤ netSum n (v k) p (t k) B) := by
        intro hkW
        have := hmax k hkW
        simp only [hb, hd] at hbd
        linarith
      have hknot : netSum n (v k) p (t k) B < t k / n - s := by
        by_contra hcon
        push_neg at hcon
        exact hkW (Finset.mem_filter.mpr ⟨hk, hcon⟩)
      rw [hsplitN] at hknot
      have hmul : (n : ℝ) * a + b < t k - (n : ℝ) * s := by
        have h := mul_lt_mul_of_pos_left hknot hn'
        have e1 : (n : ℝ) * (a + b / n) = (n : ℝ) * a + b := by field_simp
        have e2 : (n : ℝ) * (t k / n - s) = t k - (n : ℝ) * s := by field_simp
        rw [e1, e2] at h
        exact h
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (n : ℝ) - 1) ha0]
end FairSelling.EqualProceedsBagFilling
