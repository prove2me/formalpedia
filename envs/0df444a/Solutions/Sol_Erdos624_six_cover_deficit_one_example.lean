-- Prove2me | solution 1 for Erdos624.six_cover_deficit_one_example
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-19T15:08:46.499545+00:00
-- url     : https://prove2.me/submissions/aebc022d-b5d8-4d74-a2bb-03848a1e2583

import Mathlib
open Finset

namespace E624R20E
open Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Ten vertex-types and six row labels of the six-row deficit-one example.
Row `0` is `∞`; rows `1`–`5` are `ℤ/5ℤ`. Types `0`–`4` are `{∞,i,i+1}`;
types `5`–`9` are the finite triples `ℤ/5ℤ \ {i,i+2}`. -/
def rowsOf : Fin 10 → Finset (Fin 6)
  | ⟨0, _⟩ => {0, 1, 2}
  | ⟨1, _⟩ => {0, 2, 3}
  | ⟨2, _⟩ => {0, 3, 4}
  | ⟨3, _⟩ => {0, 4, 5}
  | ⟨4, _⟩ => {0, 5, 1}
  | ⟨5, _⟩ => {2, 4, 5}
  | ⟨6, _⟩ => {3, 5, 1}
  | ⟨7, _⟩ => {4, 1, 2}
  | ⟨8, _⟩ => {5, 2, 3}
  | ⟨9, _⟩ => {1, 3, 4}

lemma rowsOf_card (t : Fin 10) : #(rowsOf t) = 3 := by
  fin_cases t <;> decide

lemma types_in_row (r : Fin 6) :
    #(univ.filter (fun t : Fin 10 => r ∈ rowsOf t)) = 5 := by
  fin_cases r <;> decide

lemma types_not_covering (t₁ t₂ : Fin 10) :
    rowsOf t₁ ∪ rowsOf t₂ ≠ (univ : Finset (Fin 6)) := by
  fin_cases t₁ <;> fin_cases t₂ <;> decide

lemma pair_cooccur (r₁ r₂ : Fin 6) (hne : r₁ ≠ r₂) :
    #(univ.filter (fun t : Fin 10 => r₁ ∈ rowsOf t ∧ r₂ ∈ rowsOf t)) = 2 := by
  fin_cases r₁ <;> fin_cases r₂ <;> (first | exact (hne rfl).elim | decide)

variable {h : ℕ}

def rawRow (r : Fin 6) : Finset (Fin 10 × Fin h) :=
  univ.filter (fun p : Fin 10 × Fin h => r ∈ rowsOf p.1)

lemma rawRow_eq (r : Fin 6) :
    rawRow (h := h) r =
      (univ.filter (fun t : Fin 10 => r ∈ rowsOf t)).product
        (univ : Finset (Fin h)) := by
  ext ⟨t, s⟩
  simp [rawRow, mem_product]

lemma card_rawRow (r : Fin 6) : #(rawRow (h := h) r) = 5 * h := by
  rw [rawRow_eq, product_eq_sprod, card_product, types_in_row, card_univ, Fintype.card_fin]

lemma mem_rawRow {r : Fin 6} {p : Fin 10 × Fin h} :
    p ∈ rawRow (h := h) r ↔ r ∈ rowsOf p.1 := by
  simp [rawRow]

lemma rawRow_inter_eq (r₁ r₂ : Fin 6) :
    rawRow (h := h) r₁ ∩ rawRow (h := h) r₂ =
      (univ.filter (fun t : Fin 10 => r₁ ∈ rowsOf t ∧ r₂ ∈ rowsOf t)).product
        (univ : Finset (Fin h)) := by
  ext ⟨t, s⟩
  simp [mem_inter, mem_rawRow, mem_product]

lemma card_rawRow_inter (r₁ r₂ : Fin 6) (hne : r₁ ≠ r₂) :
    #(rawRow (h := h) r₁ ∩ rawRow (h := h) r₂) = 2 * h := by
  rw [rawRow_inter_eq, product_eq_sprod, card_product, pair_cooccur r₁ r₂ hne, card_univ, Fintype.card_fin]

lemma raw_ne (hh : 0 < h) {r₁ r₂ : Fin 6} (hne : r₁ ≠ r₂) :
    rawRow (h := h) r₁ ≠ rawRow (h := h) r₂ := by
  intro hEq
  have hinter :
      rawRow (h := h) r₁ ∩ rawRow (h := h) r₂ = rawRow (h := h) r₁ := by
    simp [hEq]
  have hcard :
      #(rawRow (h := h) r₁) = #(rawRow (h := h) r₁ ∩ rawRow (h := h) r₂) :=
    congrArg card hinter.symm
  rw [card_rawRow, card_rawRow_inter r₁ r₂ hne] at hcard
  nlinarith

variable (hh : 0 < h)

def p0 : Fin 10 × Fin h := (⟨0, by decide⟩, ⟨0, hh⟩)

lemma p0_in_row0 : p0 hh ∈ rawRow (h := h) 0 := by
  simp [p0, mem_rawRow, rowsOf]

def shrunkRow0 : Finset (Fin 10 × Fin h) := (rawRow (h := h) 0).erase (p0 hh)

def raws : Finset (Finset (Fin 10 × Fin h)) :=
  {rawRow (h := h) 1, rawRow (h := h) 2, rawRow (h := h) 3,
    rawRow (h := h) 4, rawRow (h := h) 5}

def family : Finset (Finset (Fin 10 × Fin h)) :=
  insert (shrunkRow0 hh) (raws (h := h))

lemma card_shrunk : #(shrunkRow0 hh) = 5 * h - 1 := by
  rw [shrunkRow0, card_erase_of_mem (p0_in_row0 hh), card_rawRow]

lemma shrunk_ne_raw (r : Fin 6) (hr : r ≠ 0) :
    shrunkRow0 hh ≠ rawRow (h := h) r := by
  intro hEq
  have hc : #(shrunkRow0 hh) = #(rawRow (h := h) r) := congrArg card hEq
  have : 1 ≤ 5 * h := by nlinarith
  rw [card_shrunk hh, card_rawRow] at hc
  omega

lemma mem_raws {A : Finset (Fin 10 × Fin h)} :
    A ∈ raws (h := h) ↔
      A = rawRow (h := h) 1 ∨ A = rawRow (h := h) 2 ∨ A = rawRow (h := h) 3 ∨
        A = rawRow (h := h) 4 ∨ A = rawRow (h := h) 5 := by
  simp [raws, mem_insert, mem_singleton]

lemma card_raws (hh : 0 < h) : #(raws (h := h)) = 5 := by
  have h12 : rawRow (h := h) 1 ≠ rawRow (h := h) 2 := raw_ne hh (by decide)
  have h13 : rawRow (h := h) 1 ≠ rawRow (h := h) 3 := raw_ne hh (by decide)
  have h14 : rawRow (h := h) 1 ≠ rawRow (h := h) 4 := raw_ne hh (by decide)
  have h15 : rawRow (h := h) 1 ≠ rawRow (h := h) 5 := raw_ne hh (by decide)
  have h23 : rawRow (h := h) 2 ≠ rawRow (h := h) 3 := raw_ne hh (by decide)
  have h24 : rawRow (h := h) 2 ≠ rawRow (h := h) 4 := raw_ne hh (by decide)
  have h25 : rawRow (h := h) 2 ≠ rawRow (h := h) 5 := raw_ne hh (by decide)
  have h34 : rawRow (h := h) 3 ≠ rawRow (h := h) 4 := raw_ne hh (by decide)
  have h35 : rawRow (h := h) 3 ≠ rawRow (h := h) 5 := raw_ne hh (by decide)
  have h45 : rawRow (h := h) 4 ≠ rawRow (h := h) 5 := raw_ne hh (by decide)
  have n5 : rawRow (h := h) 4 ∉ ({rawRow (h := h) 5} : Finset _) := by
    simp [h45]
  have n4 : rawRow (h := h) 3 ∉
      ({rawRow (h := h) 4, rawRow (h := h) 5} : Finset _) := by
    simp [h34, h35]
  have n3 : rawRow (h := h) 2 ∉
      ({rawRow (h := h) 3, rawRow (h := h) 4, rawRow (h := h) 5} : Finset _) := by
    simp [h23, h24, h25]
  have n2 : rawRow (h := h) 1 ∉
      ({rawRow (h := h) 2, rawRow (h := h) 3, rawRow (h := h) 4,
        rawRow (h := h) 5} : Finset _) := by
    simp [h12, h13, h14, h15]
  -- unfold raws as successive inserts (Lean parses {a,b,c,...} as insert a (insert b ...))
  simp only [raws]
  rw [card_insert_of_notMem n2, card_insert_of_notMem n3, card_insert_of_notMem n4,
      card_insert_of_notMem n5, card_singleton]

lemma shrunk_not_mem_raws : shrunkRow0 hh ∉ raws (h := h) := by
  intro hmem
  rcases mem_raws.mp hmem with h | h | h | h | h
  · exact shrunk_ne_raw hh 1 (by decide) h
  · exact shrunk_ne_raw hh 2 (by decide) h
  · exact shrunk_ne_raw hh 3 (by decide) h
  · exact shrunk_ne_raw hh 4 (by decide) h
  · exact shrunk_ne_raw hh 5 (by decide) h

lemma family_card : #(family hh) = 6 := by
  rw [family, card_insert_of_notMem (shrunk_not_mem_raws hh), card_raws hh]

lemma family_mem {A : Finset (Fin 10 × Fin h)} :
    A ∈ family hh ↔ A = shrunkRow0 hh ∨ A ∈ raws (h := h) := by
  simp [family]

lemma raw_mem_family (r : Fin 6) (hr : r ≠ 0) :
    rawRow (h := h) r ∈ family hh := by
  refine (family_mem hh).2 (Or.inr ?_)
  fin_cases r
  · exact (hr rfl).elim
  all_goals
    simp [mem_raws]

lemma family_sub (A : Finset (Fin 10 × Fin h)) (hA : A ∈ family hh) :
    A ⊆ (univ : Finset (Fin 10 × Fin h)) := fun _ _ => mem_univ _

lemma family_nonempty (A : Finset (Fin 10 × Fin h)) (hA : A ∈ family hh) :
    A.Nonempty := by
  have hpos : 1 ≤ 5 * h := by nlinarith
  rcases (family_mem hh).1 hA with h | h
  · subst h
    exact card_pos.mp (by have := card_shrunk hh; omega)
  · rcases mem_raws.mp h with h | h | h | h | h
    all_goals
      subst h
      exact card_pos.mp (by rw [card_rawRow]; nlinarith)

lemma mem_shrunk {p : Fin 10 × Fin h} :
    p ∈ shrunkRow0 hh ↔ p ∈ rawRow (h := h) 0 ∧ p ≠ p0 hh := by
  simp [shrunkRow0, mem_erase, and_comm]

lemma shrunk_inter_eq (r : Fin 6) :
    shrunkRow0 hh ∩ rawRow (h := h) r =
      (rawRow (h := h) 0 ∩ rawRow (h := h) r).erase (p0 hh) := by
  ext p
  simp [mem_inter, mem_shrunk, mem_erase]
  tauto

lemma shrunk_inter_raw_nonempty (r : Fin 6) (hr : r ≠ 0) :
    (shrunkRow0 hh ∩ rawRow (h := h) r).Nonempty := by
  have hcard0 : #(rawRow (h := h) 0 ∩ rawRow (h := h) r) = 2 * h :=
    card_rawRow_inter 0 r (by exact hr.symm)
  have hpos : 1 ≤ 2 * h := by nlinarith
  have hcard :
      #(shrunkRow0 hh ∩ rawRow (h := h) r) =
        #(rawRow (h := h) 0 ∩ rawRow (h := h) r) -
          if p0 hh ∈ rawRow (h := h) 0 ∩ rawRow (h := h) r then 1 else 0 := by
    rw [shrunk_inter_eq]
    by_cases hin : p0 hh ∈ rawRow (h := h) 0 ∩ rawRow (h := h) r
    · simp [card_erase_of_mem hin, hin]
    · simp [erase_eq_of_notMem hin, hin]
  have : 0 < #(shrunkRow0 hh ∩ rawRow (h := h) r) := by
    rw [hcard, hcard0]
    split_ifs <;> omega
  exact card_pos.mp this

lemma family_intersecting (A B : Finset (Fin 10 × Fin h))
    (hA : A ∈ family hh) (hB : B ∈ family hh) (hneAB : A ≠ B) :
    ¬ Disjoint A B := by
  have hdis_of {X Y : Finset (Fin 10 × Fin h)} (hI : (X ∩ Y).Nonempty) :
      ¬ Disjoint X Y := (not_disjoint_iff_nonempty_inter).2 hI
  have hrawI : ∀ r₁ r₂ : Fin 6, r₁ ≠ r₂ →
      (rawRow (h := h) r₁ ∩ rawRow (h := h) r₂).Nonempty := by
    intro r₁ r₂ hr
    exact card_pos.mp (by rw [card_rawRow_inter r₁ r₂ hr]; nlinarith)
  rcases (family_mem hh).1 hA with hAs | hAr
  · subst hAs
    rcases (family_mem hh).1 hB with hBs | hBr
    · exact (hneAB hBs.symm).elim
    · rcases mem_raws.mp hBr with h | h | h | h | h
      · subst h; exact hdis_of (shrunk_inter_raw_nonempty hh 1 (by decide))
      · subst h; exact hdis_of (shrunk_inter_raw_nonempty hh 2 (by decide))
      · subst h; exact hdis_of (shrunk_inter_raw_nonempty hh 3 (by decide))
      · subst h; exact hdis_of (shrunk_inter_raw_nonempty hh 4 (by decide))
      · subst h; exact hdis_of (shrunk_inter_raw_nonempty hh 5 (by decide))
  · rcases (family_mem hh).1 hB with hBs | hBr
    · subst hBs
      rcases mem_raws.mp hAr with h | h | h | h | h
      · subst h; exact hdis_of (by simpa [inter_comm] using shrunk_inter_raw_nonempty hh 1 (by decide))
      · subst h; exact hdis_of (by simpa [inter_comm] using shrunk_inter_raw_nonempty hh 2 (by decide))
      · subst h; exact hdis_of (by simpa [inter_comm] using shrunk_inter_raw_nonempty hh 3 (by decide))
      · subst h; exact hdis_of (by simpa [inter_comm] using shrunk_inter_raw_nonempty hh 4 (by decide))
      · subst h; exact hdis_of (by simpa [inter_comm] using shrunk_inter_raw_nonempty hh 5 (by decide))
    · rcases mem_raws.mp hAr with ha | ha | ha | ha | ha
      all_goals
        subst ha
        rcases mem_raws.mp hBr with hb | hb | hb | hb | hb
        all_goals
          subst hb
          first
          | exact (hneAB rfl).elim
          | exact hdis_of (hrawI _ _ (by decide))

lemma exists_row_avoiding (p q : Fin 10 × Fin h) :
    ∃ A ∈ family hh, p ∉ A ∧ q ∉ A := by
  obtain ⟨r, hr⟩ : ∃ r : Fin 6, r ∉ rowsOf p.1 ∪ rowsOf q.1 := by
    by_contra hnone
    apply types_not_covering p.1 q.1
    exact eq_univ_iff_forall.2 fun r => by
      by_contra hr
      exact hnone ⟨r, hr⟩
  have hp : r ∉ rowsOf p.1 := fun h => hr (mem_union.2 (Or.inl h))
  have hq : r ∉ rowsOf q.1 := fun h => hr (mem_union.2 (Or.inr h))
  by_cases hr0 : r = 0
  · subst r
    refine ⟨shrunkRow0 hh, (family_mem hh).2 (Or.inl rfl), ?_, ?_⟩
    · intro hp'
      exact hp (mem_rawRow.1 ((mem_shrunk hh).1 hp').1)
    · intro hq'
      exact hq (mem_rawRow.1 ((mem_shrunk hh).1 hq').1)
  · refine ⟨rawRow (h := h) r, raw_mem_family hh r hr0, ?_, ?_⟩
    · intro hp'
      exact hp (mem_rawRow.1 hp')
    · intro hq'
      exact hq (mem_rawRow.1 hq')

lemma family_covers (Y : Finset (Fin 10 × Fin h))
    (hY : Y ⊆ (univ : Finset (Fin 10 × Fin h)))
    (hcard : #Y = #(univ : Finset (Fin 10 × Fin h)) - 2) :
    ∃ A ∈ family hh, A ⊆ Y := by
  have hZ : #(univ : Finset (Fin 10 × Fin h)) = 10 * h := by
    simp [card_univ, Fintype.card_prod, Fintype.card_fin]
  have hge : 2 ≤ #(univ : Finset (Fin 10 × Fin h)) := by
    rw [hZ]; nlinarith
  -- Z \ Y has two elements
  set Z : Finset (Fin 10 × Fin h) := univ
  have hdiff : #(Z \ Y) = 2 := by
    rw [card_sdiff_of_subset hY, hcard]
    have : 2 ≤ #Z := by
      have hZ : #Z = 10 * h := by simp [Z, card_univ, Fintype.card_prod, Fintype.card_fin]
      rw [hZ]; nlinarith
    omega
  obtain ⟨p, q, hpq, hEq⟩ := card_eq_two.mp hdiff
  have hp : p ∈ Z \ Y := by simp [hEq]
  have hq : q ∈ Z \ Y := by simp [hEq]
  have hYp : p ∉ Y := (mem_sdiff.1 hp).2
  have hYq : q ∉ Y := (mem_sdiff.1 hq).2
  obtain ⟨A, hA, hpA, hqA⟩ := exists_row_avoiding hh p q
  refine ⟨A, hA, ?_⟩
  intro x hxA
  have hxZ : x ∈ Z := mem_univ _
  by_contra hxY
  have hxdiff : x ∈ Z \ Y := mem_sdiff.2 ⟨hxZ, hxY⟩
  have : x = p ∨ x = q := by
    have : x ∈ ({p, q} : Finset _) := by simpa [hEq] using hxdiff
    simpa using this
  rcases this with hxp | hxq
  · exact hpA (hxp ▸ hxA)
  · exact hqA (hxq ▸ hxA)

lemma family_sizes (A : Finset (Fin 10 × Fin h)) (hA : A ∈ family hh) :
    5 * h - 1 ≤ #A := by
  have hpos : 1 ≤ 5 * h := by nlinarith
  rcases (family_mem hh).1 hA with h | h
  · subst h
    exact le_of_eq (card_shrunk hh).symm
  · rcases mem_raws.mp h with h | h | h | h | h
    all_goals
      subst h
      rw [card_rawRow]
      exact Nat.sub_le _ _

lemma family_sum : ∑ A ∈ family hh, #A = 3 * #(univ : Finset (Fin 10 × Fin h)) - 1 := by
  have hZ : #(univ : Finset (Fin 10 × Fin h)) = 10 * h := by
    simp [card_univ, Fintype.card_prod, Fintype.card_fin]
  have hsum_raws : ∑ A ∈ raws (h := h), #A = 5 * (5 * h) := by
    have h1 : rawRow (h := h) 1 ∈ raws (h := h) := by simp [mem_raws]
    -- compute by rewriting raws as inserts and using sum_insert
    have h12 : rawRow (h := h) 1 ≠ rawRow (h := h) 2 := raw_ne hh (by decide)
    have h13 : rawRow (h := h) 1 ≠ rawRow (h := h) 3 := raw_ne hh (by decide)
    have h14 : rawRow (h := h) 1 ≠ rawRow (h := h) 4 := raw_ne hh (by decide)
    have h15 : rawRow (h := h) 1 ≠ rawRow (h := h) 5 := raw_ne hh (by decide)
    have h23 : rawRow (h := h) 2 ≠ rawRow (h := h) 3 := raw_ne hh (by decide)
    have h24 : rawRow (h := h) 2 ≠ rawRow (h := h) 4 := raw_ne hh (by decide)
    have h25 : rawRow (h := h) 2 ≠ rawRow (h := h) 5 := raw_ne hh (by decide)
    have h34 : rawRow (h := h) 3 ≠ rawRow (h := h) 4 := raw_ne hh (by decide)
    have h35 : rawRow (h := h) 3 ≠ rawRow (h := h) 5 := raw_ne hh (by decide)
    have h45 : rawRow (h := h) 4 ≠ rawRow (h := h) 5 := raw_ne hh (by decide)
    have n5 : rawRow (h := h) 4 ∉ ({rawRow (h := h) 5} : Finset _) := by simp [h45]
    have n4 : rawRow (h := h) 3 ∉
        ({rawRow (h := h) 4, rawRow (h := h) 5} : Finset _) := by simp [h34, h35]
    have n3 : rawRow (h := h) 2 ∉
        ({rawRow (h := h) 3, rawRow (h := h) 4, rawRow (h := h) 5} : Finset _) := by
      simp [h23, h24, h25]
    have n2 : rawRow (h := h) 1 ∉
        ({rawRow (h := h) 2, rawRow (h := h) 3, rawRow (h := h) 4,
          rawRow (h := h) 5} : Finset _) := by
      simp [h12, h13, h14, h15]
    simp only [raws]
    rw [sum_insert n2, sum_insert n3, sum_insert n4, sum_insert n5, sum_singleton,
        card_rawRow, card_rawRow, card_rawRow, card_rawRow, card_rawRow]
    ring
  have hsum : ∑ A ∈ family hh, #A = #(shrunkRow0 hh) + ∑ A ∈ raws (h := h), #A := by
    rw [family, sum_insert (shrunk_not_mem_raws hh)]
  rw [hsum, card_shrunk hh, hsum_raws, hZ]
  have : 1 ≤ 5 * h := by nlinarith
  omega

/-- Explicit intersecting six-cover of deficit exactly one, for every positive scale. -/
theorem six_cover_deficit_one_example (hh : 0 < h) :
    ∃ (Z : Finset (Fin 10 × Fin h)) (S : Finset (Finset (Fin 10 × Fin h))),
      #Z = 10 * h ∧ #S = 6 ∧ (∀ A ∈ S, A ⊆ Z) ∧ (∀ A ∈ S, A.Nonempty) ∧
        (∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Disjoint A B) ∧
        (∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) ∧
        (∀ A ∈ S, 5 * h - 1 ≤ #A) ∧
        (∑ A ∈ S, #A = 3 * #Z - 1) := by
  refine ⟨univ, family hh, ?_, family_card hh, family_sub hh, family_nonempty hh,
      (fun A hA B hB => family_intersecting hh A B hA hB), ?_, family_sizes hh, ?_⟩
  · simp [card_univ, Fintype.card_prod, Fintype.card_fin]
  · intro Y hY hcard
    simpa using family_covers hh Y hY hcard
  · simpa using family_sum hh

end E624R20E

namespace Erdos624

theorem six_cover_deficit_one_example (h : ℕ) (hh : 0 < h) :
    ∃ (Z : Finset (Fin 10 × Fin h)) (S : Finset (Finset (Fin 10 × Fin h))),
      #Z = 10 * h ∧ #S = 6 ∧ (∀ A ∈ S, A ⊆ Z) ∧ (∀ A ∈ S, A.Nonempty) ∧
        (∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Disjoint A B) ∧
        (∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) ∧
        (∀ A ∈ S, 5 * h - 1 ≤ #A) ∧
        (∑ A ∈ S, #A = 3 * #Z - 1) :=
  E624R20E.six_cover_deficit_one_example hh

end Erdos624

open Finset

theorem solution (h : ℕ) (hh : 0 < h) :
    ∃ (Z : Finset (Fin 10 × Fin h)) (S : Finset (Finset (Fin 10 × Fin h))),
      #Z = 10 * h ∧ #S = 6 ∧ (∀ A ∈ S, A ⊆ Z) ∧ (∀ A ∈ S, A.Nonempty) ∧
        (∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Disjoint A B) ∧
        (∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) ∧
        (∀ A ∈ S, 5 * h - 1 ≤ #A) ∧
        (∑ A ∈ S, #A = 3 * #Z - 1) :=
  Erdos624.six_cover_deficit_one_example h hh

