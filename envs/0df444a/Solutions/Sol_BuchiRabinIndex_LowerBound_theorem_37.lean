-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.theorem_37
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:12:35.978563+00:00
-- url     : https://prove2.me/submissions/20de5067-7a9c-4773-b628-fd1325340340

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_36

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Thm37Aux
open BuchiRabinIndex.LowerBound

lemma weight_le_of_mem_fullTree {n : ℕ} {x : Node} (hx : x ∈ fullTree n) :
    weight x ≤ n - 1 := by
  unfold fullTree at hx
  split_ifs at hx
  · simp at hx
  · exact (Finset.mem_filter.1 hx).2

lemma omega_eq_g (n : ℕ) (_hn : 1 ≤ n) : omega n = g n (n - 1) := by
  classical
  apply le_antisymm
  · obtain ⟨S0, hS0⟩ := (graph n).exists_isNClique_cliqueNum
    let S : Finset Node := S0.image Subtype.val
    have hmem : S ∈ (fullTree n).powerset.filter (fun (T : Finset Node) =>
        (∀ x ∈ T, weight x ≤ n - 1) ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Adj n x y) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
        exact v.property
      · intro x hx
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
        exact weight_le_of_mem_fullTree v.property
      · intro x hx y hy hne
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
        exact hS0.isClique hu hv (fun h => hne (congrArg Subtype.val h))
    have hcard : S.card = omega n := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact hS0.card_eq
    rw [← hcard]
    unfold g
    exact Finset.le_sup (f := Finset.card) hmem
  · unfold g
    refine Finset.sup_le fun S hS => ?_
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hsub, -, hclique⟩ := hS
    let S0 : Finset (Vertex n) := Finset.univ.filter fun v => v.val ∈ S
    have himg : S0.image Subtype.val = S := by
      ext x
      simp only [S0, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨v, hv, hvx⟩ => hvx ▸ hv, fun hx => ⟨⟨x, hsub hx⟩, hx, rfl⟩⟩
    have hcard : S0.card = S.card := by
      rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
    have hcl : (graph n).IsNClique S.card S0 := by
      refine ⟨?_, hcard⟩
      intro u hu v hv huv
      simp only [Finset.mem_coe, S0, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact hclique u.val hu v.val hv (fun h => huv (Subtype.ext h))
    have hbdd : BddAbove {m : ℕ | ∃ s, (graph n).IsNClique m s} :=
      ⟨Fintype.card (Vertex n), fun m ⟨T, hT⟩ => hT.2 ▸ Finset.card_le_univ T⟩
    exact le_csSup hbdd ⟨S0, hcl⟩

def F (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else if n % 2 = 0 then 2 ^ (n / 2)
  else 3 * 2 ^ ((n - 3) / 2)

lemma pow_two_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by omega) h

lemma pow_two_succ (m : ℕ) : 2 ^ (m + 1) = 2 * 2 ^ m := by
  rw [pow_succ]; ring

lemma g_formula : ∀ n, 1 ≤ n → ∀ c, c ≤ n - 1 →
    g n c = if c ≤ n / 2 then 2 ^ c else F n
  | 0, hn => by omega
  | N + 1, _ => by
      intro c hc
      by_cases hc2 : c ≤ (N + 1) / 2
      · rw [if_pos hc2]
        exact (lemma_36 (N + 1) (by omega)).1 c hc2
      · rw [if_neg hc2]
        have hN2 : 2 ≤ N := by omega
        have hc1 : 1 ≤ c := by omega
        have ih := g_formula N (by omega)
        rw [(lemma_36 (N + 1) (by omega)).2 (by omega) c hc1 hc]
        let Idx := ((Finset.range c).product (Finset.range c)).filter
          (fun ab => ab.1 + ab.2 ≤ (N + 1) - 2)
        change Idx.sup (fun ab => g N ab.1 + g N ab.2) = F (N + 1)
        by_cases hpar : N % 2 = 0
        · let k := N / 2
          have hNk : N = 2 * k := by omega
          have hk1 : 1 ≤ k := by omega
          have hFN1 : F (N + 1) = 3 * 2 ^ (k - 1) := by
            unfold F
            have h1 : ¬ N + 1 ≤ 1 := by omega
            have h2 : ¬ (N + 1) % 2 = 0 := by omega
            have h3 : (N + 1 - 3) / 2 = k - 1 := by omega
            rw [if_neg h1, if_neg h2, h3]
          have hFN : F N = 2 ^ k := by
            unfold F
            have h1 : ¬ N ≤ 1 := by omega
            rw [if_neg h1, if_pos hpar]
          have hpowk : 2 ^ k = 2 * 2 ^ (k - 1) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega]
            exact pow_two_succ (k - 1)
          rw [hFN1]
          apply le_antisymm
          · refine Finset.sup_le fun ab hab => ?_
            rcases ab with ⟨a, b⟩
            simp only [Idx, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
              Finset.mem_range] at hab
            obtain ⟨⟨ha_lt, hb_lt⟩, hab_le⟩ := hab
            have haN : a ≤ N - 1 := by omega
            have hbN : b ≤ N - 1 := by omega
            rw [ih a haN, ih b hbN, hFN]
            have hg_le_k : ∀ x, (if x ≤ N / 2 then 2 ^ x else 2 ^ k) ≤ 2 ^ k := by
              intro x
              split_ifs with hx
              · exact pow_two_le (by omega)
              · exact le_rfl
            have hmin_side : a ≤ k - 1 ∨ b ≤ k - 1 := by omega
            rcases hmin_side with hak | hbk
            · have ha_val : (if a ≤ N / 2 then 2 ^ a else 2 ^ k) ≤ 2 ^ (k - 1) := by
                rw [if_pos (by omega)]
                exact pow_two_le hak
              have hb_val := hg_le_k b
              omega
            · have hb_val : (if b ≤ N / 2 then 2 ^ b else 2 ^ k) ≤ 2 ^ (k - 1) := by
                rw [if_pos (by omega)]
                exact pow_two_le hbk
              have ha_val := hg_le_k a
              omega
          · have hmem : (k - 1, k) ∈ Idx := by
              simp only [Idx, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
                Finset.mem_range]
              exact ⟨⟨by omega, by omega⟩, by omega⟩
            have hval : g N (k - 1) + g N k = 3 * 2 ^ (k - 1) := by
              rw [ih (k - 1) (by omega), ih k (by omega), if_pos (by omega), if_pos (by omega)]
              omega
            rw [← hval]
            exact Finset.le_sup (f := fun ab : ℕ × ℕ => g N ab.1 + g N ab.2) (b := (k - 1, k)) hmem
        · let k := N / 2
          have hNk : N = 2 * k + 1 := by omega
          have hk1 : 1 ≤ k := by omega
          have hFN1 : F (N + 1) = 2 ^ (k + 1) := by
            unfold F
            have h1 : ¬ N + 1 ≤ 1 := by omega
            have h2 : (N + 1) % 2 = 0 := by omega
            have h3 : (N + 1) / 2 = k + 1 := by omega
            rw [if_neg h1, if_pos h2, h3]
          have hFN : F N = 3 * 2 ^ (k - 1) := by
            unfold F
            have h1 : ¬ N ≤ 1 := by omega
            have h3 : (N - 3) / 2 = k - 1 := by omega
            rw [if_neg h1, if_neg hpar, h3]
          have hpowk : 2 ^ k = 2 * 2 ^ (k - 1) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega]
            exact pow_two_succ (k - 1)
          have hpowk1 : 2 ^ (k + 1) = 4 * 2 ^ (k - 1) := by
            rw [pow_two_succ k, hpowk]; ring
          rw [hFN1]
          apply le_antisymm
          · refine Finset.sup_le fun ab hab => ?_
            rcases ab with ⟨a, b⟩
            simp only [Idx, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
              Finset.mem_range] at hab
            obtain ⟨⟨ha_lt, hb_lt⟩, hab_le⟩ := hab
            have haN : a ≤ N - 1 := by omega
            have hbN : b ≤ N - 1 := by omega
            rw [ih a haN, ih b hbN, hFN]
            have hg_ub : ∀ x, (if x ≤ N / 2 then 2 ^ x else 3 * 2 ^ (k - 1)) ≤ 3 * 2 ^ (k - 1) := by
              intro x
              split_ifs with hx
              · have : 2 ^ x ≤ 2 ^ k := pow_two_le (by omega)
                omega
              · exact le_rfl
            by_cases hak : a < k
            · have ha_val : (if a ≤ N / 2 then 2 ^ a else 3 * 2 ^ (k - 1)) ≤ 2 ^ (k - 1) := by
                rw [if_pos (by omega)]
                exact pow_two_le (by omega)
              have hb_val := hg_ub b
              omega
            · by_cases hbk : b < k
              · have hb_val : (if b ≤ N / 2 then 2 ^ b else 3 * 2 ^ (k - 1)) ≤ 2 ^ (k - 1) := by
                  rw [if_pos (by omega)]
                  exact pow_two_le (by omega)
                have ha_val := hg_ub a
                omega
              · have hab_eq : a = k ∧ b = k := by omega
                rcases hab_eq with ⟨rfl, rfl⟩
                rw [if_pos (by omega)]
                omega
          · have hmem : (k, k) ∈ Idx := by
              simp only [Idx, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
                Finset.mem_range]
              exact ⟨⟨by omega, by omega⟩, by omega⟩
            have hval : g N k + g N k = 2 ^ (k + 1) := by
              rw [ih k (by omega), if_pos (by omega)]
              omega
            rw [← hval]
            exact Finset.le_sup (f := fun ab : ℕ × ℕ => g N ab.1 + g N ab.2) (b := (k, k)) hmem

end BuchiRabinIndex.LowerBound.Thm37Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Thm37Aux in
theorem solution :
    omega 1 = 1 ∧
    (∀ n, 2 ≤ n →
      (Even n → omega n = 2 ^ (n / 2)) ∧
      (Odd n → omega n = 3 * 2 ^ ((n - 3) / 2))) ∧
    (∀ n c, 1 ≤ n → n / 2 < c → c ≤ n - 1 → g n c = omega n) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [omega_eq_g 1 le_rfl, g_formula 1 le_rfl 0 le_rfl]
    simp
  · intro n hn2
    rw [omega_eq_g n (by omega), g_formula n (by omega) (n - 1) le_rfl]
    by_cases hn_two : n = 2
    · subst hn_two
      constructor
      · intro _; simp
      · intro hodd
        rcases hodd with ⟨k, hk⟩
        omega
    · have hgt : ¬ n - 1 ≤ n / 2 := by omega
      rw [if_neg hgt]
      unfold F
      rw [if_neg (by omega)]
      constructor
      · rintro ⟨k, rfl⟩
        rw [if_pos (by omega)]
      · rintro ⟨k, rfl⟩
        rw [if_neg (by omega)]
  · intro n c hn1 hgt hle
    rw [omega_eq_g n hn1, g_formula n hn1 c hle, g_formula n hn1 (n - 1) le_rfl]
    rw [if_neg (by omega), if_neg (by omega)]
