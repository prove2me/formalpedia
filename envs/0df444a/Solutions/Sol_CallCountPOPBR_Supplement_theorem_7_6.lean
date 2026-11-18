-- Prove2me | solution 1 for CallCountPOPBR.Supplement.theorem_7_6
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:25:07.290513+00:00
-- url     : https://prove2.me/submissions/43af049f-0122-42f7-9bba-919b779d74a5

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_BinSpec

set_option autoImplicit false

namespace CC76Aux
open CallCountPOPBR.Supplement

lemma count_eq {β : ℕ} (s : BinSpec β) (n : ℕ) :
    s.count n = if h : β ≤ n then
      1 + Sym2.lift ⟨fun i j : Fin n => s.count i + s.count j, fun _ _ => Nat.add_comm _ _⟩ (s n h)
    else 1 := by
  unfold BinSpec.count
  rw [Nat.strongRec_eq]

lemma mem_pairSet_mk (c : ℕ → ℕ) (n : ℕ) (i j : Fin n) :
    s(i, j) ∈ pairSet c n ↔ c i + c j + 1 = c n := by
  simp [pairSet]

lemma char {β : ℕ} (c : ℕ → ℕ) (hbase : ∀ n, n < β → c n = 1) (s : BinSpec β) :
    (∀ m, s.count m = c m) ↔ ∀ n (h : β ≤ n), s n h ∈ pairSet c n := by
  constructor
  · intro hs n h
    obtain ⟨⟨i, j⟩, hz⟩ := Quot.exists_rep (s n h)
    have hz' : s n h = s(i, j) := hz.symm
    have e := count_eq s n
    rw [dif_pos h, hz', Sym2.lift_mk] at e
    rw [hz', mem_pairSet_mk]
    simp only at e
    rw [hs, hs, hs] at e
    omega
  · intro hp m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases h : β ≤ m
      · obtain ⟨⟨i, j⟩, hz⟩ := Quot.exists_rep (s m h)
        have hz' : s m h = s(i, j) := hz.symm
        have hm := hp m h
        rw [hz', mem_pairSet_mk] at hm
        rw [count_eq, dif_pos h, hz', Sym2.lift_mk]
        simp only
        rw [ih i i.2, ih j j.2]
        omega
      · rw [count_eq, dif_neg h, hbase m (by omega)]

lemma modify {β : ℕ} (s : BinSpec β) (n : ℕ) (z : Sym2 (Fin n)) :
    ∃ s' : BinSpec β, (∀ m (h : β ≤ m), m ≠ n → s' m h = s m h) ∧ ∀ h : β ≤ n, s' n h = z := by
  refine ⟨fun m hm => if hmn : m = n then Sym2.map (Fin.cast hmn.symm) z else s m hm, ?_, ?_⟩
  · intro m h hne
    simp [hne]
  · intro h
    simp

lemma modify_real {β : ℕ} (c : ℕ → ℕ) (s : BinSpec β)
    (hs : ∀ n (h : β ≤ n), s n h ∈ pairSet c n) (n : ℕ) (z : Sym2 (Fin n))
    (hz : z ∈ pairSet c n) :
    ∃ s' : BinSpec β, (∀ m (h : β ≤ m), s' m h ∈ pairSet c m) ∧ ∀ h : β ≤ n, s' n h = z := by
  obtain ⟨s', h1, h2⟩ := modify s n z
  refine ⟨s', fun m h => ?_, h2⟩
  by_cases hmn : m = n
  · subst hmn; rw [h2]; exact hz
  · rw [h1 m h hmn]; exact hs m h

end CC76Aux

open CallCountPOPBR.Supplement in
theorem solution (β : ℕ) (hβ : 1 ≤ β) (c : ℕ → ℕ)
        (hbase : ∀ n, n < β → c n = 1) :
        ((∃! s : BinSpec β, ∀ n, s.count n = c n) ↔
          ∀ n, β ≤ n → (pairSet c n).card = 1) ∧
    ((∃ s : BinSpec β, ∀ n, s.count n = c n) →
      ∀ n (h : β ≤ n),
        {z | ∃ s : BinSpec β, (∀ m, s.count m = c m) ∧ s n h = z} = (pairSet c n : Set (Sym2 (Fin n)))) ∧
    (∀ n, β ≤ n → pairSet c n = ∅ → ¬ ∃ s : BinSpec β, ∀ m, s.count m = c m) := by
  have hchar := CC76Aux.char c hbase
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨s, hs, huniq⟩ n h
    have hsP := (hchar s).mp hs
    by_contra hne
    have hpos : 0 < (pairSet c n).card := Finset.card_pos.mpr ⟨_, hsP n h⟩
    obtain ⟨z, hz, hzne⟩ := Finset.exists_mem_ne (by omega : 1 < (pairSet c n).card) (s n h)
    obtain ⟨s', hs', hs'n⟩ := CC76Aux.modify_real c s hsP n z hz
    have := huniq s' ((hchar s').mpr hs')
    apply hzne
    rw [← hs'n h, this]
  · intro hcard
    have hex : ∀ n (h : β ≤ n), ∃ a, pairSet c n = {a} := fun n h => Finset.card_eq_one.mp (hcard n h)
    choose f hf using hex
    refine ⟨f, (hchar f).mpr (fun n h => by rw [hf n h]; exact Finset.mem_singleton_self _), ?_⟩
    intro s' hs'
    have hP := (hchar s').mp hs'
    funext n h
    have := hP n h
    rw [hf n h, Finset.mem_singleton] at this
    exact this
  · rintro ⟨s, hs⟩ n h
    ext z
    simp only [Set.mem_setOf_eq, Finset.mem_coe]
    constructor
    · rintro ⟨s', hs', rfl⟩
      exact (hchar s').mp hs' n h
    · intro hz
      obtain ⟨s', hs', hs'n⟩ := CC76Aux.modify_real c s ((hchar s).mp hs) n z hz
      exact ⟨s', (hchar s').mpr hs', hs'n h⟩
  · rintro n h hempty ⟨s, hs⟩
    have := (hchar s).mp hs n h
    rw [hempty] at this
    exact Finset.notMem_empty _ this
