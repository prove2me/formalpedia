-- Prove2me | solution 1 for BulteauTranspositions.NPHard.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:27:24.103233+00:00
-- url     : https://prove2.me/submissions/98b352a9-ee30-473f-92e6-c2734a4a4512

import Definitions.Def_BulteauTranspositions_NPHard_ThreeDT

namespace Aux_BulteauTranspositions_NPHard_lemma_7

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

end Aux_BulteauTranspositions_NPHard_lemma_7

open BulteauTranspositions.NPHard Aux_BulteauTranspositions_NPHard_lemma_7 in
theorem solution (I J : Instance) (t : Triple) (p : ℕ → ℕ)
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
