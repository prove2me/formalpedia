-- Prove2me | solution 1 for CompOT.Auction.proposition_3_9
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:47:34.13944+00:00
-- url     : https://prove2.me/submissions/2d63174b-e7d1-4001-8784-858476436cfb

import Mathlib
import Definitions.Def_CompOT_Auction_Defs

open CompOT.Auction

private theorem step_injective {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) {s s' : AuctionState n}
    (hinj : ∀ a ∈ s.S, ∀ b ∈ s.S, s.ξ a = s.ξ b → a = b)
    (hs : AuctionStep C ε s s') :
    ∀ a ∈ s'.S, ∀ b ∈ s'.S, s'.ξ a = s'.ξ b → a = b := by
  rcases hs with ⟨i, hi, j₁, j₂, hj, hmin, hsecond, hg, hS, hξ⟩
  intro a ha b hb hab
  rw [hS, Finset.mem_insert, Finset.mem_filter] at ha hb
  rcases ha with hai | ⟨ha, haξ⟩
  · subst a
    rcases hb with hbi | ⟨hb, hbξ⟩
    · exact hbi.symm
    · have hbi : b ≠ i := fun h => hi (h ▸ hb)
      have heq : j₁ = s.ξ b := by
        simpa only [hξ, Function.update_self, Function.update_of_ne hbi] using hab
      exact False.elim (hbξ heq.symm)
  · have hai : a ≠ i := fun h => hi (h ▸ ha)
    rcases hb with hbi | ⟨hb, hbξ⟩
    · subst b
      have heq : s.ξ a = j₁ := by
        simpa only [hξ, Function.update_self, Function.update_of_ne hai] using hab
      exact False.elim (haξ heq)
    · have hbi : b ≠ i := fun h => hi (h ▸ hb)
      apply hinj a ha b hb
      simpa only [hξ, Function.update_of_ne hai, Function.update_of_ne hbi] using hab

private theorem run_injective {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionPrefix C ε s T) :
    ∀ t ≤ T, ∀ a ∈ (s t).S, ∀ b ∈ (s t).S, (s t).ξ a = (s t).ξ b → a = b := by
  intro t
  induction t with
  | zero =>
    intro _ a ha
    simpa [hs.1] using ha
  | succ t ih =>
    intro ht
    exact step_injective C ε (ih (by omega)) (hs.2.2 t (by omega))

private theorem step_preserves_cs {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    {ε : ℝ} (hε : 0 < ε) {s s' : AuctionState n} (hc : EpsCS C ε s)
    (hs : AuctionStep C ε s s') : EpsCS C ε s' := by
  classical
  rcases hs with ⟨i, hi, j₁, j₂, hj, hmin, hsecond, hg, hS, hξ⟩
  have hdec : ∀ j, s'.g j ≤ s.g j := by
    intro j
    rw [hg]
    by_cases h : j = j₁
    · subst j
      simp only [Function.update_self]
      linarith [hmin j₂]
    · simp [Function.update_of_ne h]
  intro k hk
  rw [hS, Finset.mem_insert, Finset.mem_filter] at hk
  rcases hk with hki | ⟨hk, hkξ⟩
  · subst k
    letI : Nonempty (Fin n) := ⟨i⟩
    have hleft : C i (s'.ξ i) - s'.g (s'.ξ i) = C i j₂ - s.g j₂ + ε := by
      rw [hξ, Function.update_self, hg, Function.update_self]
      ring
    have hlow : C i j₂ - s.g j₂ ≤ ⨅ j, (C i j - s'.g j) := by
      apply le_ciInf
      intro j
      rw [hg]
      by_cases h : j = j₁
      · subst j
        simp only [Function.update_self]
        linarith
      · rw [Function.update_of_ne h]
        exact hsecond j h
    rw [hleft]
    linarith
  · have hki : k ≠ i := by
      intro h
      subst k
      exact hi hk
    have hmono : (⨅ j, (C k j - s.g j)) ≤ ⨅ j, (C k j - s'.g j) :=
      ciInf_mono (Set.finite_range _).bddBelow (fun j => sub_le_sub_left (hdec j) _)
    have hleft : C k (s'.ξ k) - s'.g (s'.ξ k) = C k (s.ξ k) - s.g (s.ξ k) := by
      rw [hξ, Function.update_of_ne hki, hg, Function.update_of_ne hkξ]
    rw [hleft]
    linarith [hc k hk]

private theorem run_cs {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε)
    (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionPrefix C ε s T) :
    ∀ t ≤ T, EpsCS C ε (s t) := by
  intro t
  induction t with
  | zero =>
    intro _ i hi
    simpa [hs.1] using hi
  | succ t ih =>
    intro ht
    exact step_preserves_cs C hε (ih (by omega)) (hs.2.2 t (by omega))

theorem solution {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ}
    (hε : 0 < ε) (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionRun C ε s T) :
    Function.Bijective (s T).ξ ∧
      ∀ σ : Equiv.Perm (Fin n), assignmentCost C (s T).ξ ≤ assignmentCost C σ + n * ε := by
  classical
  have hall (i : Fin n) : i ∈ (s T).S := by simp [hs.2]
  have hinj : Function.Injective (s T).ξ := by
    intro a b hab
    exact run_injective C ε s T hs.1 T le_rfl a (hall a) b (hall b) hab
  have hbij : Function.Bijective (s T).ξ := hinj.bijective_of_finite
  refine ⟨hbij, ?_⟩
  intro σ
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective (s T).ξ hbij
  have hsum : ∑ i, (s T).g ((s T).ξ i) = ∑ j, (s T).g j :=
    Equiv.sum_comp π (s T).g
  have hcs := run_cs C hε s T hs.1 T le_rfl
  have hb : ∑ i, (C i ((s T).ξ i) - (s T).g ((s T).ξ i)) ≤
      ∑ i, (ε + (C i (σ i) - (s T).g (σ i))) := by
    apply Finset.sum_le_sum
    intro i _
    have hmin : (⨅ j, (C i j - (s T).g j)) ≤ C i (σ i) - (s T).g (σ i) :=
      ciInf_le (Set.finite_range _).bddBelow (σ i)
    linarith [hcs i (hall i)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  rw [hsum, Equiv.sum_comp σ (s T).g] at hb
  unfold assignmentCost
  linarith