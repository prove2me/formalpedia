-- Prove2me | solution 1 for BulteauTranspositions.NPHard.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:08:35.19984+00:00
-- url     : https://prove2.me/submissions/860c84ae-c2df-4c8f-896c-9fd839066e43

import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

namespace Aux_BulteauTranspositions_NPHard_theorem_9

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

theorem disj_aux : ∀ (l : List Triple), (l.flatMap Triple.symbols).Nodup →
    ∀ u ∈ l, ∀ v ∈ l, ∀ e, e ∈ u.symbols → e ∈ v.symbols → u = v
  | [], _, u, hu, _, _, _, _, _ => by simp at hu
  | w :: l, hN, u, hu, v, hv, e, he1, he2 => by
    rw [List.flatMap_cons, List.nodup_append] at hN
    obtain ⟨_, hN2, hd⟩ := hN
    rcases List.mem_cons.mp hu with rfl | hu' <;> rcases List.mem_cons.mp hv with rfl | hv'
    · rfl
    · exact (hd e he1 e (List.mem_flatMap.mpr ⟨v, hv', he2⟩) rfl).elim
    · exact (hd e he2 e (List.mem_flatMap.mpr ⟨u, hu', he1⟩) rfl).elim
    · exact disj_aux l hN2 u hu' v hv' e he1 he2

theorem triples_nodup : ∀ (l : List Triple), (l.flatMap Triple.symbols).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | w :: l, hN => by
    rw [List.flatMap_cons, List.nodup_append] at hN
    obtain ⟨_, hN2, hd⟩ := hN
    refine List.nodup_cons.mpr ⟨fun hw => ?_, triples_nodup l hN2⟩
    exact hd w.1 (by simp [Triple.symbols]) w.1
      (List.mem_flatMap.mpr ⟨w, hw, by simp [Triple.symbols]⟩) rfl

theorem sym_mem (I : Instance) (u : Triple) (hu : u ∈ I.triples) :
    u.1 ∈ I.symbols ∧ u.2.1 ∈ I.symbols ∧ u.2.2 ∈ I.symbols := by
  unfold Instance.symbols
  refine ⟨List.mem_flatMap.mpr ⟨u, hu, ?_⟩, List.mem_flatMap.mpr ⟨u, hu, ?_⟩,
    List.mem_flatMap.mpr ⟨u, hu, ?_⟩⟩ <;> simp [Triple.symbols]

theorem tc_cases (I : Instance) (t : Triple) :
    ((tripleCut I t).i = I.pos t.1 ∧ (tripleCut I t).j = I.pos t.2.1 ∧
      (tripleCut I t).k = I.pos t.2.2) ∨
    ((tripleCut I t).i = I.pos t.2.1 ∧ (tripleCut I t).j = I.pos t.2.2 ∧
      (tripleCut I t).k = I.pos t.1) ∨
    ((tripleCut I t).i = I.pos t.2.2 ∧ (tripleCut I t).j = I.pos t.1 ∧
      (tripleCut I t).k = I.pos t.2.1) := by
  simp only [tripleCut]
  split_ifs <;> simp

theorem inv_tau_range (n : ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    1 ≤ c.inv.tau x ∧ c.inv.tau x ≤ n := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have A := tau_cases c.inv x
  rw [inv_i, inv_j, inv_k] at A
  generalize c.inv.tau x = y at A ⊢
  omega

theorem tripleCut_eq (I : Instance) (t : Triple) (i j k : ℕ) (hij : i < j) (hjk : j < k)
    (h : (I.pos t.1 = i ∧ I.pos t.2.1 = j ∧ I.pos t.2.2 = k) ∨
      (I.pos t.1 = k ∧ I.pos t.2.1 = i ∧ I.pos t.2.2 = j) ∨
      (I.pos t.1 = j ∧ I.pos t.2.1 = k ∧ I.pos t.2.2 = i)) :
    tripleCut I t = ⟨i, j, k⟩ := by
  simp only [tripleCut]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;>
    split_ifs <;> first | rfl | omega

theorem lemma7 (I J : Instance) (t : Triple) (p : ℕ → ℕ)
    (hp : IsPermutation I.span p) (he : Equivalent I p) (hs : Step I t J) :
    Equivalent J (applyMove p (tripleCut I t)) := by
  obtain ⟨hIwf, ⟨ht, hlegal⟩, hspan, htri, hposJ⟩ := hs
  obtain ⟨_, hsymN, hrange, hinj⟩ := hIwf
  have hsymN' : (I.triples.flatMap Triple.symbols).Nodup := hsymN
  obtain ⟨c, hc⟩ : ∃ c, c = tripleCut I t := ⟨_, rfl⟩
  rw [← hc] at hlegal hposJ ⊢
  have htc := tc_cases I t
  rw [← hc] at htc
  have hlegal' := hlegal
  obtain ⟨h0, hij, hjk, hkn⟩ := hlegal'
  obtain ⟨he0, hedom, hetri⟩ := he
  obtain ⟨E1, E2, E3⟩ := hetri t ht
  have cyc : p c.j = p (c.i - 1) + 1 ∧ p c.k = p (c.j - 1) + 1 ∧ p c.i = p (c.k - 1) + 1 := by
    rcases htc with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e1, e2, e3]
    · exact ⟨E1, E2, E3⟩
    · exact ⟨E2, E3, E1⟩
    · exact ⟨E3, E1, E2⟩
  have hTN := triples_nodup _ hsymN'
  have hJmem : ∀ u, u ∈ J.triples ↔ u ≠ t ∧ u ∈ I.triples := by
    intro u
    rw [htri]
    exact hTN.mem_erase_iff
  -- symbols of J are symbols of I that avoid the positions i, j, k
  have hJsym : ∀ a ∈ J.symbols, a ∈ I.symbols ∧ I.pos a ≠ c.i ∧ I.pos a ≠ c.j ∧
      I.pos a ≠ c.k := by
    intro a ha
    obtain ⟨w, hw, haw⟩ :=
      List.mem_flatMap.mp (show a ∈ J.triples.flatMap Triple.symbols from ha)
    obtain ⟨hwt, hwI⟩ := (hJmem w).1 hw
    have haI : a ∈ I.symbols :=
      (show a ∈ I.triples.flatMap Triple.symbols from List.mem_flatMap.mpr ⟨w, hwI, haw⟩)
    obtain ⟨s1, s2, s3⟩ := sym_mem I t ht
    have n1 : I.pos a ≠ I.pos t.1 := fun h =>
      hwt (disj_aux _ hsymN' w hwI t ht a haw (by rw [hinj haI s1 h]; simp [Triple.symbols]))
    have n2 : I.pos a ≠ I.pos t.2.1 := fun h =>
      hwt (disj_aux _ hsymN' w hwI t ht a haw (by rw [hinj haI s2 h]; simp [Triple.symbols]))
    have n3 : I.pos a ≠ I.pos t.2.2 := fun h =>
      hwt (disj_aux _ hsymN' w hwI t ht a haw (by rw [hinj haI s3 h]; simp [Triple.symbols]))
    refine ⟨haI, ?_⟩
    rcases htc with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e1, e2, e3] <;>
      exact ⟨by assumption, by assumption, by assumption⟩
  have hA : ∀ a ∈ J.symbols, applyMove p c (J.pos a) = p (I.pos a) ∧
      applyMove p c (J.pos a - 1) = p (I.pos a - 1) := by
    intro a ha
    obtain ⟨haI, n1, n2, n3⟩ := hJsym a ha
    have hpos1 : 1 ≤ I.pos a := (hrange a haI).1
    simp only [applyMove, Function.comp_apply]
    rw [hposJ a ha, tau_inv _ c hlegal, tau_inv_pred _ c hlegal _ hpos1 n1 n2 n3]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · have : c.tau 0 = 0 := by
      unfold Cut.tau
      simp [h0]
    simp only [applyMove, Function.comp_apply]
    rw [this]
    exact he0
  · intro v hv hvd
    rw [hspan, Finset.mem_Icc] at hv
    have T1 := tau_cases c v
    have hu1 : 1 ≤ c.tau v ∧ c.tau v ≤ I.span := by omega
    have hvu : c.inv.tau (c.tau v) = v := inv_tau_tau _ c hlegal v
    by_cases hu3 : c.tau v = c.i ∨ c.tau v = c.j ∨ c.tau v = c.k
    · have T2 := tau_cases c (v - 1)
      have key : (c.tau v = c.i ∧ c.tau (v - 1) = c.k - 1) ∨
          (c.tau v = c.j ∧ c.tau (v - 1) = c.i - 1) ∨
          (c.tau v = c.k ∧ c.tau (v - 1) = c.j - 1) := by
        omega
      simp only [applyMove, Function.comp_apply]
      rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;> rw [k1, k2]
      · exact cyc.2.2
      · exact cyc.1
      · exact cyc.2.1
    · have hni : c.tau v ≠ c.i := fun h => hu3 (Or.inl h)
      have hnj : c.tau v ≠ c.j := fun h => hu3 (Or.inr (Or.inl h))
      have hnk : c.tau v ≠ c.k := fun h => hu3 (Or.inr (Or.inr h))
      have hnd : c.tau v ∉ I.domain := by
        intro hd
        unfold Instance.domain at hd
        rw [List.mem_toFinset, List.mem_map] at hd
        obtain ⟨a, haI, hpa⟩ := hd
        obtain ⟨w, hwI, haw⟩ :=
          List.mem_flatMap.mp (show a ∈ I.triples.flatMap Triple.symbols from haI)
        by_cases hwt : w = t
        · subst hwt
          have hpa' : I.pos a = I.pos w.1 ∨ I.pos a = I.pos w.2.1 ∨ I.pos a = I.pos w.2.2 := by
            simp only [Triple.symbols, List.mem_cons, List.not_mem_nil, or_false] at haw
            rcases haw with h | h | h <;> rw [h] <;> simp
          rcases htc with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> omega
        · have hwJ := (hJmem w).2 ⟨hwt, hwI⟩
          have haJ : a ∈ J.symbols :=
            (show a ∈ J.triples.flatMap Triple.symbols from List.mem_flatMap.mpr ⟨w, hwJ, haw⟩)
          apply hvd
          unfold Instance.domain
          rw [List.mem_toFinset, List.mem_map]
          refine ⟨a, haJ, ?_⟩
          rw [hposJ a haJ, hpa, hvu]
      have hadj := hedom (c.tau v) (Finset.mem_Icc.mpr hu1) hnd
      have := (adj_iff _ p c hlegal (c.tau v) hu1.1 hni hnj hnk).1 hadj
      rw [hvu] at this
      exact this
  · intro u hu
    obtain ⟨_, huI⟩ := (hJmem u).1 hu
    obtain ⟨s1, s2, s3⟩ := sym_mem J u hu
    obtain ⟨F1, F2, F3⟩ := hetri u huI
    obtain ⟨a1, b1⟩ := hA _ s1
    obtain ⟨a2, b2⟩ := hA _ s2
    obtain ⟨a3, b3⟩ := hA _ s3
    rw [a1, a2, a3, b1, b2, b3]
    exact ⟨F1, F2, F3⟩

theorem lemma8 (I : Instance) (hI : I.WF) (p : ℕ → ℕ)
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

theorem bp_le (n : ℕ) (p : ℕ → ℕ) (c : Cut) (hc : c.Legal n) :
    breakpoints n p ≤ breakpoints n (applyMove p c) + 3 := by
  unfold breakpoints
  set S := (Finset.Icc 1 n).filter (fun x => p x ≠ p (x - 1) + 1) with hS
  set T := (Finset.Icc 1 n).filter
    (fun x => applyMove p c x ≠ applyMove p c (x - 1) + 1) with hT
  have h1 : S.card ≤ (S \ {c.i, c.j, c.k}).card + ({c.i, c.j, c.k} : Finset ℕ).card :=
    Finset.card_le_card_sdiff_add_card
  have h2 : ({c.i, c.j, c.k} : Finset ℕ).card ≤ 3 := Finset.card_le_three
  have h3 : (S \ {c.i, c.j, c.k}).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun x => c.inv.tau x) ?_ ?_
    · intro x hx
      have hx' : x ∈ S \ {c.i, c.j, c.k} := Finset.mem_coe.mp hx
      rw [Finset.mem_sdiff, hS, Finset.mem_filter, Finset.mem_Icc] at hx'
      obtain ⟨⟨⟨hx1, hxn⟩, hne⟩, hnot⟩ := hx'
      have hxi : x ≠ c.i := fun h => hnot (by simp [h])
      have hxj : x ≠ c.j := fun h => hnot (by simp [h])
      have hxk : x ≠ c.k := fun h => hnot (by simp [h])
      obtain ⟨r1, r2⟩ := inv_tau_range n c hc x hx1 hxn
      apply Finset.mem_coe.mpr
      rw [hT, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨r1, r2⟩, ?_⟩
      intro h
      exact hne ((adj_iff n p c hc x hx1 hxi hxj hxk).mpr h)
    · intro a _ b _ hab
      have ha := tau_inv n c hc a
      have hb := tau_inv n c hc b
      have hab' : c.inv.tau a = c.inv.tau b := hab
      calc a = c.tau (c.inv.tau a) := ha.symm
        _ = c.tau (c.inv.tau b) := by rw [hab']
        _ = b := hb
  omega

theorem bp_id (n : ℕ) (q : ℕ → ℕ) (hq : ∀ x ≤ n, q x = x) : breakpoints n q = 0 := by
  unfold breakpoints
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rw [Finset.mem_Icc] at hx
  rw [hq x hx.2, hq (x - 1) (by omega)]
  omega

theorem bp_lower (n : ℕ) : ∀ (cs : List Cut) (p : ℕ → ℕ), SortingSequence n p cs →
    breakpoints n p ≤ 3 * cs.length
  | [], p, h => by
    have : breakpoints n p = 0 := bp_id n p (fun x hx => h.2 x hx)
    omega
  | c :: cs, p, h => by
    obtain ⟨hl, hs⟩ := h
    have h1 := bp_le n p c (hl c List.mem_cons_self)
    have h2 := bp_lower n cs (applyMove p c)
      ⟨fun d hd => hl d (List.mem_cons_of_mem _ hd), fun x hx => hs x hx⟩
    simp only [List.length_cons]
    omega

theorem perm_step (n : ℕ) (p : ℕ → ℕ) (hp : IsPermutation n p) (c : Cut) (hc : c.Legal n) :
    IsPermutation n (applyMove p c) := by
  obtain ⟨hn, hb, h0, hnn⟩ := hp
  have hc' := hc
  obtain ⟨c0, cij, cjk, ckn⟩ := hc'
  have hmap : Set.MapsTo c.tau (Set.Icc 0 n) (Set.Icc 0 n) := by
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    have := tau_cases c x
    omega
  have hmap' : Set.MapsTo c.inv.tau (Set.Icc 0 n) (Set.Icc 0 n) := by
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    have := tau_cases c.inv x
    rw [inv_i, inv_j, inv_k] at this
    omega
  have hinv : Set.InvOn c.inv.tau c.tau (Set.Icc 0 n) (Set.Icc 0 n) :=
    ⟨fun x _ => inv_tau_tau n c hc x, fun x _ => tau_inv n c hc x⟩
  have htau : Set.BijOn c.tau (Set.Icc 0 n) (Set.Icc 0 n) := hinv.bijOn hmap hmap'
  refine ⟨hn, hb.comp htau, ?_, ?_⟩
  · show p (c.tau 0) = 0
    have : c.tau 0 = 0 := by have := tau_cases c 0; omega
    rw [this, h0]
  · show p (c.tau n) = n
    have : c.tau n = n := by have := tau_cases c n; omega
    rw [this, hnn]

theorem bp_step (I J : Instance) (t : Triple) (p : ℕ → ℕ) (hp : IsPermutation I.span p)
    (he : Equivalent I p) (hs : Step I t J) :
    breakpoints I.span (applyMove p (tripleCut I t)) + 3 = breakpoints I.span p := by
  obtain ⟨_, ⟨ht, hlegal⟩, _, _, _⟩ := hs
  obtain ⟨c, hc⟩ : ∃ c, c = tripleCut I t := ⟨_, rfl⟩
  rw [← hc] at hlegal ⊢
  have htc := tc_cases I t
  rw [← hc] at htc
  have hlegal' := hlegal
  obtain ⟨h0, hij, hjk, hkn⟩ := hlegal'
  obtain ⟨_, _, hetri⟩ := he
  obtain ⟨E1, E2, E3⟩ := hetri t ht
  have cyc : p c.j = p (c.i - 1) + 1 ∧ p c.k = p (c.j - 1) + 1 ∧ p c.i = p (c.k - 1) + 1 := by
    rcases htc with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e1, e2, e3]
    · exact ⟨E1, E2, E3⟩
    · exact ⟨E2, E3, E1⟩
    · exact ⟨E3, E1, E2⟩
  have hpinj : Set.InjOn p (Set.Icc 0 I.span) := hp.2.1.injOn
  have inj : ∀ x y, x ≤ I.span → y ≤ I.span → p x = p y → x = y := fun x y hx hy hxy =>
    hpinj (Set.mem_Icc.mpr ⟨Nat.zero_le _, hx⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, hy⟩) hxy
  have t1 : c.tau c.i = c.j := by have := tau_cases c c.i; omega
  have t2 : c.tau (c.i - 1) = c.i - 1 := by have := tau_cases c (c.i - 1); omega
  have t3 : c.tau (c.k + c.i - c.j) = c.i := by have := tau_cases c (c.k + c.i - c.j); omega
  have t4 : c.tau (c.k + c.i - c.j - 1) = c.k - 1 := by
    have := tau_cases c (c.k + c.i - c.j - 1); omega
  have t5 : c.tau c.k = c.k := by have := tau_cases c c.k; omega
  have t6 : c.tau (c.k - 1) = c.j - 1 := by have := tau_cases c (c.k - 1); omega
  set S := (Finset.Icc 1 I.span).filter (fun x => p x ≠ p (x - 1) + 1) with hS
  set T := (Finset.Icc 1 I.span).filter
    (fun x => applyMove p c x ≠ applyMove p c (x - 1) + 1) with hT
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
      obtain ⟨r1, r2⟩ := inv_tau_range _ c hlegal x hx1 hxn
      apply Finset.mem_coe.mpr
      rw [Finset.mem_sdiff, hT, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨⟨r1, r2⟩, fun h => hne ((adj_iff _ p c hlegal x hx1 hxi hxj hxk).mpr h)⟩, ?_⟩
      intro hX'
      rw [hX] at hX'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX'
      have TT := tau_cases c (c.inv.tau x)
      have TI := tau_inv _ c hlegal x
      omega
    · intro a _ b _ hab
      have ha := tau_inv _ c hlegal a
      have hb := tau_inv _ c hlegal b
      have hab' : c.inv.tau a = c.inv.tau b := hab
      calc a = c.tau (c.inv.tau a) := ha.symm
        _ = c.tau (c.inv.tau b) := by rw [hab']
        _ = b := hb
  have hK' : (T \ X).card ≤ (S \ A).card := by
    refine Finset.card_le_card_of_injOn (fun y => c.tau y) ?_ ?_
    · intro y hy
      have hy' : y ∈ T \ X := Finset.mem_coe.mp hy
      rw [Finset.mem_sdiff, hT, Finset.mem_filter, Finset.mem_Icc] at hy'
      obtain ⟨⟨⟨hy1, hyn⟩, hne⟩, hnot⟩ := hy'
      have hy2 : y ≠ c.k + c.i - c.j ∧ y ≠ c.i ∧ y ≠ c.k := by
        refine ⟨fun h => hnot ?_, fun h => hnot ?_, fun h => hnot ?_⟩ <;> rw [hX, h] <;> simp
      have TC := tau_cases c y
      have hx1 : 1 ≤ c.tau y := by omega
      have hxn : c.tau y ≤ I.span := by omega
      have hxi : c.tau y ≠ c.i := by omega
      have hxj : c.tau y ≠ c.j := by omega
      have hxk : c.tau y ≠ c.k := by omega
      have hyy := inv_tau_tau _ c hlegal y
      apply Finset.mem_coe.mpr
      rw [Finset.mem_sdiff, hS, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨⟨hx1, hxn⟩, fun h => hne ?_⟩, ?_⟩
      · have := (adj_iff _ p c hlegal (c.tau y) hx1 hxi hxj hxk).mp h
        rw [hyy] at this
        exact this
      · intro hA'
        rw [hA] at hA'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hA'
        omega
    · intro a _ b _ hab
      have hab' : c.tau a = c.tau b := hab
      calc a = c.inv.tau (c.tau a) := (inv_tau_tau _ c hlegal a).symm
        _ = c.inv.tau (c.tau b) := by rw [hab']
        _ = b := inv_tau_tau _ c hlegal b
  have hAS : A ⊆ S := by
    intro x hx
    rw [hA] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    rcases hx with rfl | rfl | rfl
    · refine ⟨⟨by omega, by omega⟩, fun h => ?_⟩
      have := inj _ _ (by omega) (by omega) (h.trans cyc.1.symm)
      omega
    · refine ⟨⟨by omega, by omega⟩, fun h => ?_⟩
      have := inj _ _ (by omega) (by omega) (h.trans cyc.2.1.symm)
      omega
    · refine ⟨⟨by omega, by omega⟩, fun h => ?_⟩
      have := inj _ _ (by omega) (by omega) (h.trans cyc.2.2.symm)
      omega
  have hXT : ∀ x ∈ X, x ∉ T := by
    intro x hx hxT
    rw [hT, Finset.mem_filter] at hxT
    apply hxT.2
    rw [hX] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [applyMove, Function.comp_apply]
    rcases hx with rfl | rfl | rfl
    · rw [t3, t4]; exact cyc.2.2
    · rw [t1, t2]; exact cyc.1
    · rw [t5, t6]; exact cyc.2.1
  have h1 := Finset.card_sdiff_add_card_inter S A
  have h2 := Finset.card_sdiff_add_card_inter T X
  have hSA : (S ∩ A).card = 3 := by
    rw [Finset.inter_eq_right.mpr hAS, hA]
    exact Finset.card_eq_three.mpr ⟨c.i, c.j, c.k, by omega, by omega, by omega, rfl⟩
  have hTX : (T ∩ X).card = 0 := by
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_of_forall_notMem
      (fun x hx => hXT x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx).1)
  show T.card + 3 = S.card
  omega

theorem flatMap_erase_sublist : ∀ (l : List Triple) (a : Triple),
    ((l.erase a).flatMap Triple.symbols).Sublist (l.flatMap Triple.symbols)
  | [], a => by simp
  | b :: l, a => by
    by_cases hb : b = a
    · subst hb
      rw [List.erase_cons_head, List.flatMap_cons]
      exact List.sublist_append_right _ _
    · rw [List.erase_cons_tail (by simpa using hb), List.flatMap_cons, List.flatMap_cons]
      exact (flatMap_erase_sublist l a).append_left _

theorem step_exists (I : Instance) (hI : I.WF) (t : Triple) (hw : WellOrdered I t) :
    ∃ J, Step I t J ∧ J.WF := by
  refine ⟨⟨I.span, I.triples.erase t, fun a => (tripleCut I t).inv.tau (I.pos a)⟩,
    ⟨hI, hw, rfl, rfl, fun a _ => rfl⟩, ?_⟩
  obtain ⟨hn, hsym, hrange, hinj⟩ := hI
  have hl := hw.2
  have hsub : ∀ a, a ∈ (I.triples.erase t).flatMap Triple.symbols → a ∈ I.symbols :=
    fun a ha => (flatMap_erase_sublist I.triples t).subset ha
  refine ⟨hn, (flatMap_erase_sublist I.triples t).nodup hsym, ?_, ?_⟩
  · intro a ha
    exact inv_tau_range _ _ hl _ (hrange a (hsub a ha)).1 (hrange a (hsub a ha)).2
  · intro a ha b hb hab
    apply hinj (hsub a ha) (hsub b hb)
    have := congrArg (tripleCut I t).tau hab
    simp only [tau_inv _ _ hl] at this
    exact this

theorem bp_pos (I : Instance) (hI : I.WF) (p : ℕ → ℕ) (hp : IsPermutation I.span p)
    (he : Equivalent I p) (t : Triple) (ht : t ∈ I.triples) : 0 < breakpoints I.span p := by
  obtain ⟨_, hsym, hrange, hinj⟩ := hI
  have hsym' : (I.triples.flatMap Triple.symbols).Nodup := hsym
  obtain ⟨s1, s2, _⟩ := sym_mem I t ht
  have r1 := hrange _ s1
  have r2 := hrange _ s2
  have hnd : [t.1, t.2.1, t.2.2].Nodup := (List.nodup_flatMap.mp hsym').1 t ht
  have hne : t.1 ≠ t.2.1 := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have hpne : I.pos t.1 ≠ I.pos t.2.1 := fun h => hne (hinj s1 s2 h)
  have E1 := (he.2.2 t ht).1
  unfold breakpoints
  apply Finset.card_pos.mpr
  refine ⟨I.pos t.1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨r1.1, r1.2⟩, fun h => hpne ?_⟩⟩
  exact hp.2.1.injOn (Set.mem_Icc.mpr ⟨Nat.zero_le _, r1.2⟩)
    (Set.mem_Icc.mpr ⟨Nat.zero_le _, r2.2⟩) (h.trans E1.symm)

theorem fwd (J : Instance) (hJ : J.triples = []) :
    ∀ U, Relation.ReflTransGen (fun U V => ∃ t, Step U t V) U J →
      ∀ p, IsPermutation U.span p → Equivalent U p →
        ∃ cs, SortingSequence U.span p cs ∧ cs.length = U.triples.length ∧
          breakpoints U.span p = 3 * U.triples.length := by
  intro U hU
  induction hU using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro p _ he
    have hid : ∀ x ≤ J.span, p x = x := by
      intro x
      induction x with
      | zero => intro _; exact he.1
      | succ m ih =>
        intro hm
        have hdom : m + 1 ∉ J.domain := by
          unfold Instance.domain Instance.symbols
          rw [hJ]
          simp
        have := he.2.1 (m + 1) (Finset.mem_Icc.mpr ⟨by omega, hm⟩) hdom
        rw [this, Nat.add_sub_cancel, ih (by omega)]
    refine ⟨[], ⟨by simp, fun x hx => hid x hx⟩, by simp [hJ], ?_⟩
    simp [hJ, bp_id _ _ hid]
  | @head U V hstep hrest ih =>
    intro p hp he
    obtain ⟨t, hs⟩ := hstep
    have hs' := hs
    obtain ⟨_, hwo, hspan, htri, _⟩ := hs'
    have hq := perm_step _ p hp _ hwo.2
    have heq := lemma7 U V t p hp he hs
    obtain ⟨cs, ⟨hl, hsort⟩, hlen, hbp⟩ :=
      ih (applyMove p (tripleCut U t)) (by rw [hspan]; exact hq) heq
    have hbp3 := bp_step U V t p hp he hs
    have hlenV : V.triples.length + 1 = U.triples.length := by
      have := List.length_pos_of_mem hwo.1
      rw [htri, List.length_erase_of_mem hwo.1]
      omega
    rw [hspan] at hl hsort hbp
    refine ⟨tripleCut U t :: cs, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hwo.2
      · exact hl d hd
    · intro x hx
      exact hsort x hx
    · simp only [List.length_cons]
      omega
    · omega

theorem bwd : ∀ (L : ℕ) (I : Instance) (p : ℕ → ℕ) (cs : List Cut), I.WF →
    IsPermutation I.span p → Equivalent I p → SortingSequence I.span p cs →
    cs.length = L → breakpoints I.span p = 3 * L → Collapsible I
  | 0, I, p, _, hI, hp, he, _, _, hbp => by
    refine ⟨I, Relation.ReflTransGen.refl, ?_⟩
    cases hT : I.triples with
    | nil => rfl
    | cons t rest =>
      have ht : t ∈ I.triples := by rw [hT]; exact List.mem_cons_self
      have := bp_pos I hI p hp he t ht
      exfalso
      omega
  | L + 1, I, p, cs, hI, hp, he, hsort, hlen, hbp => by
    obtain ⟨hl, hs⟩ := hsort
    cases cs with
    | nil => simp at hlen
    | cons c cs' =>
      have hc : c.Legal I.span := hl c List.mem_cons_self
      have hsort' : SortingSequence I.span (applyMove p c) cs' :=
        ⟨fun d hd => hl d (List.mem_cons_of_mem _ hd), fun x hx => hs x hx⟩
      have hlen' : cs'.length = L := by
        simp only [List.length_cons] at hlen
        omega
      have hlow := bp_lower I.span cs' (applyMove p c) hsort'
      have hle := bp_le I.span p c hc
      have hd : breakpoints I.span (applyMove p c) + 3 = breakpoints I.span p := by omega
      obtain ⟨t, ht, hwo, htau⟩ := lemma8 I hI p hp he c hc hd
      obtain ⟨J, hstep, hJwf⟩ := step_exists I hI t hwo
      have hstep' := hstep
      obtain ⟨_, _, hspan, _, _⟩ := hstep'
      have hmove : applyMove p (tripleCut I t) = applyMove p c := by
        funext x
        show p ((tripleCut I t).tau x) = p (c.tau x)
        rw [htau]
      have heqJ : Equivalent J (applyMove p c) := by
        rw [← hmove]
        exact lemma7 I J t p hp he hstep
      have hpJ : IsPermutation J.span (applyMove p c) := by
        rw [hspan]
        exact perm_step _ p hp c hc
      have hsJ : SortingSequence J.span (applyMove p c) cs' := by
        rw [hspan]
        exact hsort'
      have hbJ : breakpoints J.span (applyMove p c) = 3 * L := by
        rw [hspan]
        omega
      obtain ⟨K, hJK, hK⟩ := bwd L J (applyMove p c) cs' hJwf hpJ heqJ hsJ hlen' hbJ
      exact ⟨K, Relation.ReflTransGen.head ⟨t, hstep⟩ hJK, hK⟩

end Aux_BulteauTranspositions_NPHard_theorem_9

open BulteauTranspositions.NPHard Aux_BulteauTranspositions_NPHard_theorem_9 in
theorem solution (I : Instance) (hI : I.WF) (p : ℕ → ℕ)
    (hp : IsPermutation I.span p) (he : Equivalent I p) :
    Collapsible I ↔ distance I.span p = (I.triples.length : ℕ∞) ∧
      3 * I.triples.length = breakpoints I.span p := by
  constructor
  · rintro ⟨J, hIJ, hJ⟩
    obtain ⟨cs, hsort, hlen, hbp⟩ := fwd J hJ I hIJ p hp he
    refine ⟨?_, hbp.symm⟩
    unfold distance
    apply le_antisymm
    · apply sInf_le
      exact ⟨cs, hsort, by rw [hlen]⟩
    · apply le_sInf
      rintro k ⟨cs', hs', rfl⟩
      have := bp_lower _ cs' p hs'
      exact_mod_cast (show I.triples.length ≤ cs'.length by omega)
  · rintro ⟨hd, hb⟩
    have hlt : distance I.span p < ((I.triples.length + 1 : ℕ) : ℕ∞) := by
      rw [hd]
      exact_mod_cast Nat.lt_succ_self _
    unfold distance at hlt
    obtain ⟨k, ⟨cs, hs, rfl⟩, hk⟩ := sInf_lt_iff.mp hlt
    have hk' : cs.length < I.triples.length + 1 := by exact_mod_cast hk
    have := bp_lower _ cs p hs
    exact bwd cs.length I p cs hI hp he hs rfl (by omega)
