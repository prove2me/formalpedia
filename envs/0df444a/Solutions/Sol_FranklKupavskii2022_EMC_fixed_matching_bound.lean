-- Prove2me | solution 1 for FranklKupavskii2022.EMC.fixed_matching_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:57:04.515499+00:00
-- url     : https://prove2.me/submissions/4157c2e9-8ebf-42e0-a154-556ed8734fbc

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_tMatchings
import Definitions.Def_FranklKupavskii2022_EMC_CrossDependent
import Definitions.Def_FranklKupavskii2022_EMC_Nested

namespace FranklKupavskii2022.EMC

/-- Greedy system of distinct representatives for nested families. -/
theorem aux_fmb_sdr {α : Type*} [DecidableEq α] (d : α) :
    ∀ (n : ℕ) (S : ℕ → Finset α), (∀ i j, 1 ≤ i → i ≤ j → j ≤ n → S j ⊆ S i) →
      (∀ i, 1 ≤ i → i ≤ n → n + 1 - i ≤ (S i).card) →
      ∃ p : ℕ → α, (∀ i, 1 ≤ i → i ≤ n → p i ∈ S i) ∧
        ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → p i ≠ p j := by
  intro n
  induction n with
  | zero =>
    intro S _ _
    exact ⟨fun _ => d, fun i h1 h2 => by omega, fun i j h1 h2 => by omega⟩
  | succ n ih =>
    intro S hS hc
    have hne : (S (n+1)).Nonempty := by
      rw [← Finset.card_pos]; have := hc (n+1) (by omega) le_rfl; omega
    obtain ⟨c, hc'⟩ := hne
    obtain ⟨p, hp1, hp2⟩ := ih (fun i => (S i).erase c)
      (fun i j h1 h2 h3 => Finset.erase_subset_erase c (hS i j h1 h2 (by omega)))
      (fun i h1 h2 => by
        have h := hc i h1 (by omega)
        have := Finset.pred_card_le_card_erase (s := S i) (a := c)
        omega)
    refine ⟨fun i => if i = n + 1 then c else p i, ?_, ?_⟩
    · intro i h1 h2
      by_cases h : i = n + 1
      · subst h; simp [hc']
      · simp only [h, if_false]
        exact Finset.mem_of_mem_erase (hp1 i h1 (by omega))
    · intro i j h1 h2 h3 h4 hij
      by_cases hi : i = n + 1 <;> by_cases hj : j = n + 1
      · exact absurd (hi.trans hj.symm) hij
      · simp only [hi, hj, if_true, if_false]
        have := hp1 j h3 (by omega)
        intro h
        rw [← h] at this
        exact (Finset.notMem_erase c (S j)) this
      · simp only [hi, hj, if_true, if_false]
        have := hp1 i h1 (by omega)
        intro h
        rw [h] at this
        exact (Finset.notMem_erase c (S i)) this
      · simp only [hi, hj, if_false]
        exact hp2 i j h1 (by omega) h3 (by omega) hij

theorem aux_fmb_exists (s t : ℕ) (Fam : ℕ → Finset (Finset ℕ))
    (hcross : CrossDependent s Fam) (hnest : Nested s Fam)
    (B : Fin t → Finset ℕ)
    (hBdisj : ∀ i j : Fin t, i ≠ j → Disjoint (B i) (B j)) :
    ∃ i0, 1 ≤ i0 ∧ i0 ≤ s + 1 ∧ eta (Fam i0) B ≤ s + 1 - i0 := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have ht : 0 < t := by
    have h := hcon (s+1) (by omega) le_rfl
    unfold eta at h
    have h2 : (Finset.univ.filter (fun i : Fin t => B i ∈ Fam (s+1))).card ≤ t :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    omega
  let S : ℕ → Finset (Fin t) := fun i => Finset.univ.filter (fun k => B k ∈ Fam i)
  obtain ⟨p, hp1, hp2⟩ := aux_fmb_sdr (⟨0, ht⟩ : Fin t) (s+1) S
    (fun i j hi hij hj k hk => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hnest i j hi hij hj hk)
    (fun i hi1 hi2 => by
      have h := hcon i hi1 hi2
      unfold eta at h
      simp only [S]
      omega)
  apply hcross
  refine ⟨fun i => B (p i), ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_Icc] at hi
    have := hp1 i hi.1 hi.2
    simpa [S] using this
  · intro i hi j hj hij
    rw [Finset.mem_Icc] at hi hj
    exact hBdisj _ _ (hp2 i j hi.1 hi.2 hj.1 hj.2 hij)

end FranklKupavskii2022.EMC

open FranklKupavskii2022.EMC

theorem solution (s t l : ℕ) (x q : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ s + 1) (hq1 : 1 ≤ q)
    (hq2 : q ≤ s + 1) (ht : (s : ℝ) + x + 1 ≤ t) (Y : Finset ℕ) (Fam : ℕ → Finset (Finset ℕ))
    (hFam : ∀ i ∈ Finset.Icc 1 (s + 1), Fam i ⊆ Y.powersetCard l)
    (hcross : CrossDependent s Fam) (hnest : Nested s Fam) (hY : t * l ≤ Y.card)
    (B : Fin t → Finset ℕ) (hB : ∀ j, B j ∈ Y.powersetCard l)
    (hBdisj : ∀ i j : Fin t, i ≠ j → Disjoint (B i) (B j)) :
    (x ≤ (eta (Fam (s + 1)) B : ℝ) →
        ∑ i ∈ Finset.Icc 1 s, (eta (Fam i) B : ℝ) + q * eta (Fam (s + 1)) B ≤
          s * t + q * eta (Fam (s + 1)) B - s * x) ∧
      ((eta (Fam (s + 1)) B : ℝ) ≤ x →
        ∑ i ∈ Finset.Icc 1 s, (eta (Fam i) B : ℝ) + q * eta (Fam (s + 1)) B ≤
          s * t - eta (Fam (s + 1)) B * (x - q * eta (Fam (s + 1)) B / (s + 1))) := by
  classical
  obtain ⟨i0, h1, h2, h3⟩ := aux_fmb_exists s t Fam hcross hnest B hBdisj
  have hle_t : ∀ i, eta (Fam i) B ≤ t := fun i => by
    unfold eta; exact le_trans (Finset.card_filter_le _ _) (by simp)
  have hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ s + 1 → eta (Fam j) B ≤ eta (Fam i) B := by
    intro i j hi hij hj
    unfold eta
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hnest i j hi hij hj hk
  have hIcc : Finset.Icc 1 s = Finset.Ico 1 (s + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hsum : ∑ i ∈ Finset.Icc 1 s, eta (Fam i) B ≤
      (i0 - 1) * t + (s + 1 - i0) * (s + 1 - i0) := by
    rw [hIcc, ← Finset.sum_Ico_consecutive _ h1 h2]
    have e1 : ∑ i ∈ Finset.Ico 1 i0, eta (Fam i) B ≤ (i0 - 1) * t := by
      have := Finset.sum_le_card_nsmul (Finset.Ico 1 i0) (fun i => eta (Fam i) B) t
        (fun i _ => hle_t i)
      simpa [Nat.card_Ico] using this
    have e2 : ∑ i ∈ Finset.Ico i0 (s + 1), eta (Fam i) B ≤ (s + 1 - i0) * (s + 1 - i0) := by
      have := Finset.sum_le_card_nsmul (Finset.Ico i0 (s + 1)) (fun i => eta (Fam i) B)
        (s + 1 - i0) (fun i hi => by
          rw [Finset.mem_Ico] at hi
          exact le_trans (hmono i0 i h1 hi.1 (by omega)) h3)
      simpa [Nat.card_Ico] using this
    omega
  -- pass to reals
  set j : ℕ := s + 1 - i0 with hjdef
  have hjs : j ≤ s := by omega
  have hi0 : i0 - 1 = s - j := by omega
  rw [hi0] at hsum
  have haj : eta (Fam (s + 1)) B ≤ j := le_trans (hmono i0 (s+1) h1 h2 le_rfl) h3
  have hA : ∑ i ∈ Finset.Icc 1 s, (eta (Fam i) B : ℝ) ≤ ((s : ℝ) - j) * t + (j : ℝ) * j := by
    have := (Nat.cast_le (α := ℝ)).mpr hsum
    push_cast [Nat.cast_sum, Nat.cast_sub hjs] at this
    exact this
  set A := ∑ i ∈ Finset.Icc 1 s, (eta (Fam i) B : ℝ) with hAdef
  set a : ℝ := (eta (Fam (s + 1)) B : ℝ) with hadef
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have haj' : a ≤ (j : ℝ) := by rw [hadef]; exact_mod_cast haj
  have hjs' : (j : ℝ) ≤ s := by exact_mod_cast hjs
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  refine ⟨fun hxa => ?_, fun hax => ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr (le_trans hxa haj')) (sub_nonneg.mpr hjs'),
      mul_nonneg hj0 (show (0:ℝ) ≤ t - s - x - 1 by linarith)]
  · set r : ℝ := q * a / (s + 1) with hrdef
    have hs1 : (0 : ℝ) < s + 1 := by positivity
    have hr : r * (s + 1) = q * a := by rw [hrdef]; field_simp
    have hra : r ≤ a := by
      rw [hrdef, div_le_iff₀ hs1]
      nlinarith [mul_le_mul_of_nonneg_left hq2 ha0]
    nlinarith [mul_nonneg hj0 (show (0:ℝ) ≤ t - s - x - 1 by linarith),
      mul_nonneg (sub_nonneg.mpr haj') (show (0:ℝ) ≤ s + x + 1 - j - a by linarith),
      mul_nonneg (sub_nonneg.mpr hra) (show (0:ℝ) ≤ s + 1 - a by linarith)]
