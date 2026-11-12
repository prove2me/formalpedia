-- Prove2me | solution 1 for FairShares.kpw18_no_mms_allocation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:24:07.67776+00:00
-- url     : https://prove2.me/submissions/e50cfbf5-6fd1-4eb2-97c3-9ba54fb60d68

import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_FairShares_bundle
import Definitions.Def_LittleCharity_MMS_Setting

namespace Aux_FairShares_kpw18
open FairShares

private def wN (i : Fin 3) : ℕ → ℕ
  | 0 => if i = 0 then 26 else if i = 1 then 26 else 25
  | 1 => if i = 0 then 23 else if i = 1 then 22 else 23
  | 2 => if i = 0 then 19 else 20
  | 3 => if i = 0 then 16 else if i = 1 then 16 else 15
  | 4 => if i = 0 then 12 else 13
  | 5 => if i = 1 then 9 else 10
  | 6 => 9
  | 7 => 4
  | 8 => 1
  | _ => 0

private def wFin (i : Fin 3) (g : Fin 9) : ℕ := wN i g.1

private def rem (i : Fin 3) : ℕ → ℕ
  | 0 => 0
  | r + 1 => wN i (8 - r) + rem i r

private def tailAlloc (A : Fin 9 → Fin 3) (i : Fin 3) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
    (if h : 8 - r < 9 then if A ⟨8 - r, h⟩ = i then wN i (8 - r) else 0 else 0) +
      tailAlloc A i r

private lemma tailAlloc_le_rem (A : Fin 9 → Fin 3) (i : Fin 3) :
    ∀ r : ℕ, tailAlloc A i r ≤ rem i r
  | 0 => le_rfl
  | r + 1 => by
    unfold tailAlloc rem
    have ih := tailAlloc_le_rem A i r
    split_ifs <;> omega

private def search : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, s0, s1, s2 => decide (40 ≤ s0 ∧ 40 ≤ s1 ∧ 40 ≤ s2)
  | r + 1, s0, s1, s2 =>
    if s0 + rem 0 (r + 1) < 40 ∨ s1 + rem 1 (r + 1) < 40 ∨ s2 + rem 2 (r + 1) < 40 then
      false
    else
      search r (s0 + wN 0 (8 - r)) s1 s2 ||
        search r s0 (s1 + wN 1 (8 - r)) s2 ||
        search r s0 s1 (s2 + wN 2 (8 - r))

private lemma search_complete (A : Fin 9 → Fin 3) :
    ∀ (r : ℕ) (_hr : r ≤ 9) (s0 s1 s2 : ℕ),
      40 ≤ s0 + tailAlloc A 0 r →
      40 ≤ s1 + tailAlloc A 1 r →
      40 ≤ s2 + tailAlloc A 2 r →
      search r s0 s1 s2 = true
  | 0, _, s0, s1, s2, h0, h1, h2 => by
    simp only [tailAlloc, add_zero] at h0 h1 h2
    simp [search, h0, h1, h2]
  | r + 1, hr, s0, s1, s2, h0, h1, h2 => by
    have hb0 := tailAlloc_le_rem A 0 (r + 1)
    have hb1 := tailAlloc_le_rem A 1 (r + 1)
    have hb2 := tailAlloc_le_rem A 2 (r + 1)
    have hn : ¬ (s0 + rem 0 (r + 1) < 40 ∨ s1 + rem 1 (r + 1) < 40 ∨ s2 + rem 2 (r + 1) < 40) :=
      by omega
    unfold search
    rw [if_neg hn]
    have hlt : 8 - r < 9 := by omega
    simp only [tailAlloc, hlt, ↓reduceDIte] at h0 h1 h2
    have hr' : r ≤ 9 := by omega
    have hcases : A ⟨8 - r, hlt⟩ = 0 ∨ A ⟨8 - r, hlt⟩ = 1 ∨ A ⟨8 - r, hlt⟩ = 2 := by
      generalize A ⟨8 - r, hlt⟩ = x
      fin_cases x <;> simp
    rcases hcases with hA0 | hA1 | hA2
    · have h01 : (0 : Fin 3) ≠ 1 := by decide
      have h02 : (0 : Fin 3) ≠ 2 := by decide
      have h0' : 40 ≤ (s0 + wN 0 (8 - r)) + tailAlloc A 0 r := by
        simp only [hA0, ↓reduceIte] at h0; omega
      have h1' : 40 ≤ s1 + tailAlloc A 1 r := by
        simp only [hA0, h01, ↓reduceIte, zero_add] at h1; exact h1
      have h2' : 40 ≤ s2 + tailAlloc A 2 r := by
        simp only [hA0, h02, ↓reduceIte, zero_add] at h2; exact h2
      rw [search_complete A r hr' _ _ _ h0' h1' h2']
      simp
    · have h10 : (1 : Fin 3) ≠ 0 := by decide
      have h12 : (1 : Fin 3) ≠ 2 := by decide
      have h0' : 40 ≤ s0 + tailAlloc A 0 r := by
        simp only [hA1, h10, ↓reduceIte, zero_add] at h0; exact h0
      have h1' : 40 ≤ (s1 + wN 1 (8 - r)) + tailAlloc A 1 r := by
        simp only [hA1, ↓reduceIte] at h1; omega
      have h2' : 40 ≤ s2 + tailAlloc A 2 r := by
        simp only [hA1, h12, ↓reduceIte, zero_add] at h2; exact h2
      rw [search_complete A r hr' _ _ _ h0' h1' h2']
      simp
    · have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      have h0' : 40 ≤ s0 + tailAlloc A 0 r := by
        simp only [hA2, h20, ↓reduceIte, zero_add] at h0; exact h0
      have h1' : 40 ≤ s1 + tailAlloc A 1 r := by
        simp only [hA2, h21, ↓reduceIte, zero_add] at h1; exact h1
      have h2' : 40 ≤ (s2 + wN 2 (8 - r)) + tailAlloc A 2 r := by
        simp only [hA2, ↓reduceIte] at h2; omega
      rw [search_complete A r hr' _ _ _ h0' h1' h2']
      simp

private lemma search_nine_false : search 9 0 0 0 = false := by decide

private lemma tailAlloc_nine (A : Fin 9 → Fin 3) (i : Fin 3) :
    tailAlloc A i 9 = ∑ g ∈ bundle A i, wFin i g := by
  unfold bundle
  rw [Finset.sum_filter]
  have huniv : (Finset.univ : Finset (Fin 9)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8} := by decide
  rw [huniv]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rfl

private def witnessPart : Fin 3 → Fin 9 → Fin 3
  | 0 => ![1, 0, 2, 0, 2, 1, 2, 1, 0]
  | 1 => ![0, 2, 1, 1, 0, 2, 2, 1, 0]
  | _ => ![0, 1, 2, 0, 1, 2, 2, 1, 2]

private lemma witness_sum_eq (i j : Fin 3) :
    (∑ g ∈ Finset.univ.filter (fun g : Fin 9 => witnessPart i g = j), wFin i g) = 40 := by
  fin_cases i <;> fin_cases j <;> decide

private noncomputable def vs9 (i : Fin 3) (S : Finset (Fin 9)) : ℝ :=
  ∑ g ∈ S, (wFin i g : ℝ)

private lemma mms_ge_40 (i : Fin 3) :
    (40 : ℝ) ≤ LittleCharity.MMS.mms (vs9 i) 3 Finset.univ := by
  have hmms : LittleCharity.MMS.mms (vs9 i) 3 Finset.univ =
      ⨆ f : Fin 9 → Fin 3, ⨅ j : Fin 3, vs9 i (Finset.univ.filter (fun g => f g = j)) := by
    unfold LittleCharity.MMS.mms
    congr 1
  rw [hmms]
  refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) (witnessPart i))
  refine le_ciInf fun j => ?_
  have h40 := witness_sum_eq i j
  unfold vs9
  rw [← Nat.cast_sum, h40]
  norm_num

end Aux_FairShares_kpw18

open FairShares Aux_FairShares_kpw18

theorem solution :
    ∃ m : ℕ, ∃ vs : Fin 3 → (Finset (Fin m) → ℝ), (∀ i, IsAdditive (vs i)) ∧
      ¬ ∃ A : Fin m → Fin 3, ∀ i, LittleCharity.MMS.mms (vs i) 3 Finset.univ ≤ vs i (bundle A i) := by
  refine ⟨9, vs9, fun i => ⟨fun g => (wFin i g : ℝ), fun _ => Nat.cast_nonneg _, fun _ => rfl⟩, ?_⟩
  rintro ⟨A, hA⟩
  have hnat : ∀ i : Fin 3, 40 ≤ tailAlloc A i 9 := by
    intro i
    rw [tailAlloc_nine]
    have hi : (40 : ℝ) ≤ vs9 i (bundle A i) := (mms_ge_40 i).trans (hA i)
    unfold vs9 at hi
    rw [← Nat.cast_sum] at hi
    exact_mod_cast hi
  have htrue := search_complete A 9 le_rfl 0 0 0
    (by simpa using hnat 0) (by simpa using hnat 1) (by simpa using hnat 2)
  rw [search_nine_false] at htrue
  exact Bool.false_ne_true htrue
