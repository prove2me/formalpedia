-- Prove2me | solution 1 for BulteauTranspositions.NPHard.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:02:14.523356+00:00
-- url     : https://prove2.me/submissions/05872146-9ba6-4dd4-9511-846a82d47db6

import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

namespace Aux_BulteauTranspositions_NPHard_lemma_8

open BulteauTranspositions.NPHard

theorem tau_cases (c : Cut) (y : ℕ) :
    (y < c.i ∧ c.tau y = y) ∨
    (c.i ≤ y ∧ y < c.k + c.i - c.j ∧ c.tau y = y + c.j - c.i) ∨
    (c.i ≤ y ∧ c.k + c.i - c.j ≤ y ∧ y < c.k ∧ c.tau y = y + c.j - c.k) ∨
    (c.i ≤ y ∧ c.k + c.i - c.j ≤ y ∧ c.k ≤ y ∧ c.tau y = y) := by
  unfold Cut.tau
  split_ifs <;> omega

theorem inv_i (c : Cut) : c.inv.i = c.i := rfl
theorem inv_j (c : Cut) : c.inv.j = c.k + c.i - c.j := rfl
theorem inv_k (c : Cut) : c.inv.k = c.k := rfl

theorem tau_inv (n : ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) : c.tau (c.inv.tau x) = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have A := tau_cases c.inv x
  rw [inv_i, inv_j, inv_k] at A
  have B := tau_cases c (c.inv.tau x)
  generalize c.inv.tau x = y at A B ⊢
  generalize c.tau y = z at B ⊢
  omega

theorem inv_tau_tau (n : ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) : c.inv.tau (c.tau x) = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have A := tau_cases c x
  have B := tau_cases c.inv (c.tau x)
  rw [inv_i, inv_j, inv_k] at B
  generalize c.tau x = y at A B ⊢
  generalize c.inv.tau y = z at B ⊢
  omega

theorem tau_inv_pred (n : ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) (hx1 : 1 ≤ x)
    (hxi : x ≠ c.i) (hxj : x ≠ c.j) (hxk : x ≠ c.k) :
    c.tau (c.inv.tau x - 1) = x - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have A := tau_cases c.inv x
  rw [inv_i, inv_j, inv_k] at A
  have B := tau_cases c (c.inv.tau x - 1)
  generalize c.inv.tau x = y at A B ⊢
  generalize c.tau (y - 1) = z at B ⊢
  omega

theorem adj_iff (n : ℕ) (p : ℕ → ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) (hx1 : 1 ≤ x)
    (hxi : x ≠ c.i) (hxj : x ≠ c.j) (hxk : x ≠ c.k) :
    (p x = p (x - 1) + 1) ↔
      (applyMove p c (c.inv.tau x) = applyMove p c (c.inv.tau x - 1) + 1) := by
  simp only [applyMove, Function.comp_apply]
  rw [tau_inv n c hc x, tau_inv_pred n c hc x hx1 hxi hxj hxk]

theorem inv_tau_range (n : ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    1 ≤ c.inv.tau x ∧ c.inv.tau x ≤ n := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have A := tau_cases c.inv x
  rw [inv_i, inv_j, inv_k] at A
  generalize c.inv.tau x = y at A ⊢
  omega

theorem sym_mem (I : Instance) (u : Triple) (hu : u ∈ I.triples) :
    u.1 ∈ I.symbols ∧ u.2.1 ∈ I.symbols ∧ u.2.2 ∈ I.symbols := by
  unfold Instance.symbols
  refine ⟨List.mem_flatMap.mpr ⟨u, hu, ?_⟩, List.mem_flatMap.mpr ⟨u, hu, ?_⟩,
    List.mem_flatMap.mpr ⟨u, hu, ?_⟩⟩ <;> simp [Triple.symbols]

theorem tripleCut_eq (I : Instance) (t : Triple) (i j k : ℕ) (hij : i < j) (hjk : j < k)
    (h : (I.pos t.1 = i ∧ I.pos t.2.1 = j ∧ I.pos t.2.2 = k) ∨
      (I.pos t.1 = k ∧ I.pos t.2.1 = i ∧ I.pos t.2.2 = j) ∨
      (I.pos t.1 = j ∧ I.pos t.2.1 = k ∧ I.pos t.2.2 = i)) :
    tripleCut I t = ⟨i, j, k⟩ := by
  simp only [tripleCut]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;>
    split_ifs <;> first | rfl | omega

end Aux_BulteauTranspositions_NPHard_lemma_8

open BulteauTranspositions.NPHard Aux_BulteauTranspositions_NPHard_lemma_8 in
theorem solution (I : Instance) (hI : I.WF) (p : ℕ → ℕ)
    (hp : IsPermutation I.span p) (he : Equivalent I p) (c : Cut) (hc : c.Legal I.span)
    (hd : breakpoints I.span (applyMove p c) + 3 = breakpoints I.span p) :
    ∃ t ∈ I.triples, WellOrdered I t ∧ c.tau = (tripleCut I t).tau := by
  obtain ⟨_, hsymN, hrange, hinj⟩ := hI
  have hc' := hc
  obtain ⟨h0, hij, hjk, hkn⟩ := hc'
  set S := (Finset.Icc 1 I.span).filter (fun x => p x ≠ p (x - 1) + 1) with hS
  set T := (Finset.Icc 1 I.span).filter
    (fun x => applyMove p c x ≠ applyMove p c (x - 1) + 1) with hT
  have hbS : breakpoints I.span p = S.card := rfl
  have hbT : breakpoints I.span (applyMove p c) = T.card := rfl
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A = {c.i, c.j, c.k} := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Finset ℕ, X = {c.k + c.i - c.j, c.i, c.k} := ⟨_, rfl⟩
  have hK : (S \ A).card ≤ (T \ X).card := by
    refine Finset.card_le_card_of_injOn (fun x => c.inv.tau x) ?_ ?_
    · intro x hx
      have hx' : x ∈ S \ A := Finset.mem_coe.mp hx
      rw [Finset.mem_sdiff, hS, Finset.mem_filter, Finset.mem_Icc] at hx'
      obtain ⟨⟨⟨hx1, hxn⟩, hne⟩, hnot⟩ := hx'
      have hxi : x ≠ c.i := fun h => hnot (by rw [hA]; simp [h])
      have hxj : x ≠ c.j := fun h => hnot (by rw [hA]; simp [h])
      have hxk : x ≠ c.k := fun h => hnot (by rw [hA]; simp [h])
      obtain ⟨r1, r2⟩ := inv_tau_range _ c hc x hx1 hxn
      apply Finset.mem_coe.mpr
      rw [Finset.mem_sdiff, hT, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨⟨r1, r2⟩, fun h => hne ((adj_iff _ p c hc x hx1 hxi hxj hxk).mpr h)⟩, ?_⟩
      intro hX'
      rw [hX] at hX'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX'
      have TT := tau_cases c (c.inv.tau x)
      have TI := tau_inv _ c hc x
      omega
    · intro a _ b _ hab
      have ha := tau_inv _ c hc a
      have hb := tau_inv _ c hc b
      have hab' : c.inv.tau a = c.inv.tau b := hab
      calc a = c.tau (c.inv.tau a) := ha.symm
        _ = c.tau (c.inv.tau b) := by rw [hab']
        _ = b := hb
  have h1 := Finset.card_sdiff_add_card_inter S A
  have h2 := Finset.card_sdiff_add_card_inter T X
  have h3 : (S ∩ A).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_right : S ∩ A ⊆ A)
    rw [hA] at this ⊢
    exact this.trans Finset.card_le_three
  have hSA : (S ∩ A).card = 3 := by omega
  have hTX : (T ∩ X).card = 0 := by omega
  have hAS : A ⊆ S := by
    have hA3 : A.card ≤ (S ∩ A).card := by
      rw [hSA, hA]
      exact Finset.card_le_three
    have heq := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hA3
    intro x hx
    rw [← heq] at hx
    exact (Finset.mem_inter.mp hx).1
  have hXT : ∀ x ∈ X, x ∉ T := by
    intro x hx hxT
    have hm : x ∈ T ∩ X := Finset.mem_inter.mpr ⟨hxT, hx⟩
    rw [Finset.card_eq_zero.mp hTX] at hm
    simp at hm
  have adjq : ∀ x ∈ X, applyMove p c x = applyMove p c (x - 1) + 1 := by
    intro x hx
    by_contra hne
    apply hXT x hx
    have hx2 := hx
    rw [hX] at hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    rw [hT, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hne⟩
  have t1 : c.tau c.i = c.j := by have := tau_cases c c.i; omega
  have t2 : c.tau (c.i - 1) = c.i - 1 := by have := tau_cases c (c.i - 1); omega
  have t3 : c.tau (c.k + c.i - c.j) = c.i := by have := tau_cases c (c.k + c.i - c.j); omega
  have t4 : c.tau (c.k + c.i - c.j - 1) = c.k - 1 := by
    have := tau_cases c (c.k + c.i - c.j - 1); omega
  have t5 : c.tau c.k = c.k := by have := tau_cases c c.k; omega
  have t6 : c.tau (c.k - 1) = c.j - 1 := by have := tau_cases c (c.k - 1); omega
  have A1 : p c.j = p (c.i - 1) + 1 := by
    have := adjq c.i (by rw [hX]; simp)
    simp only [applyMove, Function.comp_apply] at this
    rw [t1, t2] at this
    exact this
  have A2 : p c.i = p (c.k - 1) + 1 := by
    have := adjq (c.k + c.i - c.j) (by rw [hX]; simp)
    simp only [applyMove, Function.comp_apply] at this
    rw [t3, t4] at this
    exact this
  have A3 : p c.k = p (c.j - 1) + 1 := by
    have := adjq c.k (by rw [hX]; simp)
    simp only [applyMove, Function.comp_apply] at this
    rw [t5, t6] at this
    exact this
  have hiS : c.i ∈ S := hAS (by rw [hA]; simp)
  rw [hS, Finset.mem_filter] at hiS
  obtain ⟨he0, hedom, hetri⟩ := he
  have hdom : c.i ∈ I.domain := by
    by_contra hnd
    exact hiS.2 (hedom c.i hiS.1 hnd)
  unfold Instance.domain at hdom
  rw [List.mem_toFinset, List.mem_map] at hdom
  obtain ⟨a, ha, hpa⟩ := hdom
  obtain ⟨t, ht, hat⟩ :=
    List.mem_flatMap.mp (show a ∈ I.triples.flatMap Triple.symbols from ha)
  obtain ⟨E1, E2, E3⟩ := hetri t ht
  have hpinj : Set.InjOn p (Set.Icc 0 I.span) := hp.2.1.injOn
  obtain ⟨s1, s2, s3⟩ := sym_mem I t ht
  have r1 := hrange _ s1
  have r2 := hrange _ s2
  have r3 := hrange _ s3
  have inj : ∀ x y, x ≤ I.span → y ≤ I.span → p x = p y → x = y := fun x y hx hy hxy =>
    hpinj (Set.mem_Icc.mpr ⟨Nat.zero_le _, hx⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, hy⟩) hxy
  have hat' : a = t.1 ∨ a = t.2.1 ∨ a = t.2.2 := by
    simpa [Triple.symbols] using hat
  have key : (I.pos t.1 = c.i ∧ I.pos t.2.1 = c.j ∧ I.pos t.2.2 = c.k) ∨
      (I.pos t.1 = c.k ∧ I.pos t.2.1 = c.i ∧ I.pos t.2.2 = c.j) ∨
      (I.pos t.1 = c.j ∧ I.pos t.2.1 = c.k ∧ I.pos t.2.2 = c.i) := by
    rcases hat' with rfl | rfl | rfl
    · have q1 : I.pos t.2.1 = c.j := by
        apply inj _ c.j r2.2 (by omega)
        rw [E1, hpa, A1]
      have q2 : I.pos t.2.2 = c.k := by
        apply inj _ c.k r3.2 (by omega)
        rw [E2, q1, A3]
      exact Or.inl ⟨hpa, q1, q2⟩
    · have q1 : I.pos t.2.2 = c.j := by
        apply inj _ c.j r3.2 (by omega)
        rw [E2, hpa, A1]
      have q2 : I.pos t.1 = c.k := by
        apply inj _ c.k r1.2 (by omega)
        rw [E3, q1, A3]
      exact Or.inr (Or.inl ⟨q2, hpa, q1⟩)
    · have q1 : I.pos t.1 = c.j := by
        apply inj _ c.j r1.2 (by omega)
        rw [E3, hpa, A1]
      have q2 : I.pos t.2.1 = c.k := by
        apply inj _ c.k r2.2 (by omega)
        rw [E1, q1, A3]
      exact Or.inr (Or.inr ⟨q1, q2, hpa⟩)
  have htc := tripleCut_eq I t c.i c.j c.k hij hjk key
  refine ⟨t, ht, ⟨ht, ?_⟩, ?_⟩
  · rw [htc]
    exact hc
  · calc c.tau = Cut.tau ⟨c.i, c.j, c.k⟩ := rfl
      _ = (tripleCut I t).tau := by rw [htc]
