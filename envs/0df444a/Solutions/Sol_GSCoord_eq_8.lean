-- Prove2me | solution 1 for GSCoord.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:27:41.45726+00:00
-- url     : https://prove2.me/submissions/050702bd-7d5a-4858-8fe5-9821d7ffb4ea

import Mathlib
import Definitions.Def_GSCoord_Model

namespace Aux_GSCoord_eq8
open GSCoord

lemma chain0 (S : ℕ → ℤ) (T : ℕ → ℕ) : ∀ n k, (∀ j, k ≤ j → j < k + n → S j - S (j + 1) ≤ (T j : ℤ)) →
    S k ≤ S (k + n) + ∑ j ∈ Finset.Ico k (k + n), (T j : ℤ) := by
  intro n
  induction n with
  | zero => intro k _; simp
  | succ n ih =>
    intro k h
    have h1 := h k le_rfl (by omega)
    have h2 := ih (k + 1) (fun j hj1 hj2 => h j (by omega) (by omega))
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : k < k + (n + 1))]
    rw [show k + 1 + n = k + (n + 1) by omega] at h2
    linarith

lemma chain (S : ℕ → ℤ) (T : ℕ → ℕ) (a k b : ℕ) (hak : a ≤ k) (hkb : k ≤ b)
    (h : ∀ j, a ≤ j → j < b → S j - S (j + 1) ≤ (T j : ℤ)) :
    S k ≤ S b + ∑ j ∈ Finset.Ico a b, (T j : ℤ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkb
  have h1 := chain0 S T n k (fun j hj1 hj2 => h j (by omega) hj2)
  have h2 : ∑ j ∈ Finset.Ico k (k + n), (T j : ℤ) ≤ ∑ j ∈ Finset.Ico a (k + n), (T j : ℤ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hak)
      (fun _ _ _ => Nat.cast_nonneg _)
  linarith

lemma attain (a b : ℕ) (Feas : (ℕ → ℤ) → Prop) (C : (ℕ → ℤ) → ℝ)
    (hC : ∀ S S', (∀ k, a ≤ k → k ≤ b → S k = S' k) → C S = C S')
    (L U : ℤ) (hb : ∀ S, Feas S → ∀ k, a ≤ k → k ≤ b → L ≤ S k ∧ S k ≤ U) :
    (⨅ (S : ℕ → ℤ) (_ : Feas S), ((C S : ℝ) : EReal)) = ⊤ ∨
      ∃ S, Feas S ∧ (⨅ (S : ℕ → ℤ) (_ : Feas S), ((C S : ℝ) : EReal)) = C S := by
  classical
  let ext : (Fin (b + 1 - a) → Finset.Icc L U) → ℕ → ℤ := fun t k =>
    if h : a ≤ k ∧ k ≤ b then (t ⟨k - a, by omega⟩).1 else 0
  let V : Set ℝ := {x | ∃ S, Feas S ∧ C S = x}
  have hV : V ⊆ Set.range (fun t => C (ext t)) := by
    rintro x ⟨S, hS, rfl⟩
    have hmem : ∀ i : Fin (b + 1 - a), S (a + i) ∈ Finset.Icc L U := by
      intro i
      have hi := i.isLt
      exact Finset.mem_Icc.2 (hb S hS (a + i) (by omega) (by omega))
    refine ⟨fun i => ⟨S (a + i), hmem i⟩, ?_⟩
    dsimp only
    apply hC
    intro k hk1 hk2
    simp only [ext, dif_pos (And.intro hk1 hk2)]
    congr 1
    omega
  have hfin : V.Finite := (Set.finite_range _).subset hV
  by_cases hne : V.Nonempty
  · right
    obtain ⟨x0, hx0, hmin⟩ := Set.exists_min_image V id hfin hne
    obtain ⟨S0, hS0, rfl⟩ := hx0
    refine ⟨S0, hS0, le_antisymm (iInf₂_le S0 hS0) (le_iInf₂ fun S hS => ?_)⟩
    exact EReal.coe_le_coe_iff.2 (hmin _ ⟨S, hS, rfl⟩)
  · left
    refine le_antisymm le_top (le_iInf₂ fun S hS => ?_)
    exact absurd ⟨_, S, hS, rfl⟩ hne

lemma stage_congr (sys : SerialSystem) (S S' : ℕ → ℤ) (k : ℕ) (h1 : S k = S' k)
    (h2 : S (k + 1) = S' (k + 1)) : stageCost sys S k = stageCost sys S' k := by
  unfold stageCost netRepl; rw [h1, h2]

lemma Icc_split (N₁ N : ℕ) (h : N₁ < N) :
    Finset.Icc 1 N = Finset.Icc 1 N₁ ∪ Finset.Icc (N₁ + 1) N := by
  ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega

lemma cost_split (sys : SerialSystem) (N₁ : ℕ) (h : N₁ < sys.N) (S : ℕ → ℤ) :
    costP sys S = costP1 sys N₁ S + costP2 sys N₁ S := by
  unfold costP costP1 costP2
  rw [Icc_split N₁ sys.N h, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x h1 h2
  simp only [Finset.mem_Icc] at h1 h2
  omega

end Aux_GSCoord_eq8

open GSCoord Aux_GSCoord_eq8 in
theorem solution (sys : SerialSystem) (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN₁N : N₁ < sys.N) :
    IsLeast {v : EReal | ∃ SB : ℤ, 0 ≤ SB ∧ v = valP1 sys N₁ SB + valP2 sys N₁ SB}
      (valP sys) := by
  -- attainment for the three problems
  have hP : valP sys = ⊤ ∨ ∃ S, FeasibleP sys S ∧ valP sys = costP sys S := by
    apply attain 1 (sys.N + 1) (FeasibleP sys) (costP sys)
      (fun S S' h => Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_Icc] at hk
        exact stage_congr sys S S' k (h k (by omega) (by omega)) (h (k + 1) (by omega) (by omega)))
      (min sys.s₁ (min sys.sNplus1 0))
      (sys.sNplus1 + ∑ j ∈ Finset.Ico 1 (sys.N + 1), (sys.T j : ℤ))
    intro S ⟨h1, h2, h3, h4⟩ k hk1 hk2
    constructor
    · rcases Nat.lt_or_ge k 2 with hk | hk
      · obtain rfl : k = 1 := by omega
        rw [h1]; exact min_le_left _ _
      · rcases Nat.lt_or_ge k (sys.N + 1) with hk' | hk'
        · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
            (h4 k (Finset.mem_Icc.2 ⟨hk, by omega⟩))
        · obtain rfl : k = sys.N + 1 := by omega
          rw [h2]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    · have := chain S sys.T 1 k (sys.N + 1) hk1 hk2
        (fun j hj1 hj2 => h3 j (Finset.mem_Icc.2 ⟨hj1, by omega⟩))
      rw [h2] at this; exact this
  have h1 : ∀ SB : ℤ, valP1 sys N₁ SB = ⊤ ∨
      ∃ S, FeasibleP1 sys N₁ SB S ∧ valP1 sys N₁ SB = costP1 sys N₁ S := by
    intro SB
    apply attain 1 (N₁ + 1) (FeasibleP1 sys N₁ SB) (costP1 sys N₁)
      (fun S S' h => Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_Icc] at hk
        exact stage_congr sys S S' k (h k (by omega) (by omega)) (h (k + 1) (by omega) (by omega)))
      (min sys.s₁ (min SB 0)) (SB + ∑ j ∈ Finset.Ico 1 (N₁ + 1), (sys.T j : ℤ))
    intro S ⟨e1, e2, e3, e4⟩ k hk1 hk2
    constructor
    · rcases Nat.lt_or_ge k 2 with hk | hk
      · obtain rfl : k = 1 := by omega
        rw [e1]; exact min_le_left _ _
      · rcases Nat.lt_or_ge k (N₁ + 1) with hk' | hk'
        · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
            (e4 k (Finset.mem_Icc.2 ⟨hk, by omega⟩))
        · obtain rfl : k = N₁ + 1 := by omega
          rw [e2]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    · have := chain S sys.T 1 k (N₁ + 1) hk1 hk2
        (fun j hj1 hj2 => e3 j (Finset.mem_Icc.2 ⟨hj1, by omega⟩))
      rw [e2] at this; exact this
  have h2 : ∀ SB : ℤ, valP2 sys N₁ SB = ⊤ ∨
      ∃ S, FeasibleP2 sys N₁ SB S ∧ valP2 sys N₁ SB = costP2 sys N₁ S := by
    intro SB
    apply attain (N₁ + 1) (sys.N + 1) (FeasibleP2 sys N₁ SB) (costP2 sys N₁)
      (fun S S' h => Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_Icc] at hk
        exact stage_congr sys S S' k (h k (by omega) (by omega)) (h (k + 1) (by omega) (by omega)))
      (min SB (min sys.sNplus1 0))
      (sys.sNplus1 + ∑ j ∈ Finset.Ico (N₁ + 1) (sys.N + 1), (sys.T j : ℤ))
    intro S ⟨e1, e2, e3, e4⟩ k hk1 hk2
    constructor
    · rcases Nat.lt_or_ge k (N₁ + 2) with hk | hk
      · obtain rfl : k = N₁ + 1 := by omega
        rw [e1]; exact min_le_left _ _
      · rcases Nat.lt_or_ge k (sys.N + 1) with hk' | hk'
        · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
            (e4 k (Finset.mem_Icc.2 ⟨hk, by omega⟩))
        · obtain rfl : k = sys.N + 1 := by omega
          rw [e2]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    · have := chain S sys.T (N₁ + 1) k (sys.N + 1) hk1 hk2
        (fun j hj1 hj2 => e3 j (Finset.mem_Icc.2 ⟨hj1, by omega⟩))
      rw [e2] at this; exact this
  -- lower bound
  have lower : ∀ SB : ℤ, 0 ≤ SB → valP sys ≤ valP1 sys N₁ SB + valP2 sys N₁ SB := by
    intro SB hSB
    rcases h1 SB with e1 | ⟨S1, f1, e1⟩ <;> rcases h2 SB with e2 | ⟨S2, f2, e2⟩
    · rw [e1, e2, EReal.top_add_top]; exact le_top
    · rw [e1, e2, EReal.top_add_coe]; exact le_top
    · rw [e1, e2, EReal.coe_add_top]; exact le_top
    · rw [e1, e2, ← EReal.coe_add]
      classical
      set G : ℕ → ℤ := fun k => if k ≤ N₁ + 1 then S1 k else S2 k with hG
      obtain ⟨a1, a2, a3, a4⟩ := f1
      obtain ⟨b1, b2, b3, b4⟩ := f2
      have G1 : ∀ k, k ≤ N₁ + 1 → G k = S1 k := fun k hk => by simp [hG, hk]
      have G2 : ∀ k, N₁ + 1 < k → G k = S2 k := fun k hk => by
        simp [hG, show ¬ k ≤ N₁ + 1 by omega]
      have GB : G (N₁ + 1) = S2 (N₁ + 1) := by rw [G1 _ le_rfl, a2, b1]
      have hfeas : FeasibleP sys G := by
        refine ⟨by rw [G1 1 (by omega), a1], by rw [G2 _ (by omega), b2], fun k hk => ?_,
          fun k hk => ?_⟩
        · simp only [Finset.mem_Icc] at hk
          rcases Nat.lt_or_ge k (N₁ + 1) with hk' | hk'
          · rw [G1 k (by omega), G1 (k + 1) (by omega)]
            exact a3 k (Finset.mem_Icc.2 ⟨hk.1, by omega⟩)
          · rcases Nat.lt_or_ge (N₁ + 1) k with hk'' | hk''
            · rw [G2 k hk'', G2 (k + 1) (by omega)]
              exact b3 k (Finset.mem_Icc.2 ⟨by omega, hk.2⟩)
            · obtain rfl : k = N₁ + 1 := by omega
              rw [GB, G2 _ (by omega)]
              exact b3 _ (Finset.mem_Icc.2 ⟨le_rfl, hk.2⟩)
        · simp only [Finset.mem_Icc] at hk
          rcases Nat.lt_or_ge k (N₁ + 1) with hk' | hk'
          · rw [G1 k (by omega)]; exact a4 k (Finset.mem_Icc.2 ⟨hk.1, by omega⟩)
          · rcases Nat.lt_or_ge (N₁ + 1) k with hk'' | hk''
            · rw [G2 k hk'']; exact b4 k (Finset.mem_Icc.2 ⟨by omega, hk.2⟩)
            · obtain rfl : k = N₁ + 1 := by omega
              rw [G1 _ le_rfl, a2]; exact hSB
      have hcost : costP sys G = costP1 sys N₁ S1 + costP2 sys N₁ S2 := by
        rw [cost_split sys N₁ hN₁N G]
        congr 1
        · unfold costP1
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_Icc] at hk
          exact stage_congr sys G S1 k (G1 k (by omega)) (G1 (k + 1) (by omega))
        · unfold costP2
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_Icc] at hk
          apply stage_congr sys G S2 k _ (G2 (k + 1) (by omega))
          rcases Nat.lt_or_ge (N₁ + 1) k with hk'' | hk''
          · exact G2 k hk''
          · obtain rfl : k = N₁ + 1 := by omega
            exact GB
      rw [← hcost]
      unfold valP
      exact iInf₂_le G hfeas
  refine ⟨?_, ?_⟩
  · rcases hP with eP | ⟨S, fS, eP⟩
    · refine ⟨0, le_rfl, ?_⟩
      have := lower 0 le_rfl
      rw [eP] at this ⊢
      exact (top_le_iff.1 this).symm
    · obtain ⟨c1, c2, c3, c4⟩ := fS
      have hSB : 0 ≤ S (N₁ + 1) := c4 _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      refine ⟨S (N₁ + 1), hSB, le_antisymm (lower _ hSB) ?_⟩
      have f1 : FeasibleP1 sys N₁ (S (N₁ + 1)) S :=
        ⟨c1, rfl, fun k hk => c3 k (by simp only [Finset.mem_Icc] at hk ⊢; omega),
          fun k hk => c4 k (by simp only [Finset.mem_Icc] at hk ⊢; omega)⟩
      have f2 : FeasibleP2 sys N₁ (S (N₁ + 1)) S :=
        ⟨rfl, c2, fun k hk => c3 k (by simp only [Finset.mem_Icc] at hk ⊢; omega),
          fun k hk => c4 k (by simp only [Finset.mem_Icc] at hk ⊢; omega)⟩
      rw [eP, cost_split sys N₁ hN₁N S, EReal.coe_add]
      exact add_le_add (iInf₂_le S f1) (iInf₂_le S f2)
  · rintro v ⟨SB, hSB, rfl⟩
    exact lower SB hSB
