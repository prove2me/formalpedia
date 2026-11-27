-- Prove2me | solution 1 for Erdos287.four_reciprocal_merge_bands_amplify_omissions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:54:14.92439+00:00
-- url     : https://prove2.me/submissions/774c3444-5d4b-4159-b4fc-dabfc27a1f06

import Mathlib
import Theorems.Thm_Erdos287_min_card_reciprocal_merge_omission_mass

open Finset

set_option autoImplicit false
set_option maxHeartbeats 0

/-- Four exact reciprocal identities transport omissions from a narrow lower
band into disjoint neighborhoods higher in the interval. -/
theorem solution (D T : Finset ℕ) (m M l u : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card)
    (hl : 0 < l) (hu : 100 * u ≤ 101 * l)
    (hT : ∀ t ∈ T, l ≤ t ∧ t ≤ u ∧ m ≤ 45045 * t ∧ 108108 * t ≤ M) :
    let L := T.filter (fun t => 45045 * t ∉ D)
    let R := (Finset.Icc m M).filter (fun n => n ∉ D ∧
      77220 * l ≤ n + 1 ∧ n ≤ 108108 * u + 1)
    4 * L.card ≤ R.card ∧
      (7 / 4 : ℚ) * (∑ t ∈ L, (1 : ℚ) / ((45045 * t : ℕ) : ℚ)) ≤
        ∑ n ∈ R, (1 : ℚ) / n := by
  classical
  intro L R
  let A : Fin 4 → ℕ := ![77220, 80080, 81900, 83160]
  let B : Fin 4 → ℕ := ![108108, 102960, 100100, 98280]
  let near (i : Fin 4) (n : ℕ) : Prop :=
    (A i * l ≤ n + 1 ∧ n ≤ A i * u + 1) ∨
      (B i * l ≤ n + 1 ∧ n ≤ B i * u + 1)
  let H (i : Fin 4) := (Finset.Icc m M).filter (fun n => n ∉ D ∧ near i n)
  have hAlo (i : Fin 4) : 77220 ≤ A i := by fin_cases i <;> norm_num [A]
  have hAhi (i : Fin 4) : A i ≤ 108108 := by fin_cases i <;> norm_num [A]
  have hBlo (i : Fin 4) : 77220 ≤ B i := by fin_cases i <;> norm_num [B]
  have hBhi (i : Fin 4) : B i ≤ 108108 := by fin_cases i <;> norm_num [B]
  have transfer (i : Fin 4) :
      L.card ≤ (H i).card ∧
      (∑ t ∈ L, (1 : ℚ) / ((B i * t + 1 : ℕ) : ℚ)) ≤
        ∑ n ∈ H i, (1 : ℚ) / n := by
    apply Erdos287.min_card_reciprocal_merge_omission_mass D T m M l u
      hm hD hcover hsum hmin (A i) (B i) 45045
    · have := hAlo i
      omega
    · fin_cases i <;> norm_num [A, B]
    · have := hAlo i
      omega
    · fin_cases i <;> norm_num [A, B]
    · exact hl
    · fin_cases i <;> norm_num [A, B] <;> omega
    · intro t ht
      obtain ⟨hlt, htu, hmt, htm⟩ := hT t ht
      exact ⟨hlt, htu, hmt, (Nat.mul_le_mul_right t (hBhi i)).trans htm⟩
  have hdisj : ∀ i ∈ (univ : Finset (Fin 4)), ∀ j ∈ (univ : Finset (Fin 4)),
      i ≠ j → Disjoint (H i) (H j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hi : near i n := (mem_filter.mp hn).2.2
    have hj : near j n := (mem_filter.mp hn').2.2
    dsimp only [near] at hi hj
    fin_cases i <;> fin_cases j <;>
      simp [A, B] at hij hi hj <;>
      rcases hi with a | a <;> rcases hj with b | b <;> omega
  have hsub : (univ : Finset (Fin 4)).biUnion H ⊆ R := by
    intro n hn
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hn
    obtain ⟨hRange, hnD, hnNear⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨hRange, hnD, ?_⟩
    rcases hnNear with h | h
    · exact ⟨(Nat.mul_le_mul_right l (hAlo i)).trans h.1,
        h.2.trans (Nat.add_le_add_right (Nat.mul_le_mul_right u (hAhi i)) 1)⟩
    · exact ⟨(Nat.mul_le_mul_right l (hBlo i)).trans h.1,
        h.2.trans (Nat.add_le_add_right (Nat.mul_le_mul_right u (hBhi i)) 1)⟩
  constructor
  · calc
      4 * L.card = ∑ _ : Fin 4, L.card := by simp
      _ ≤ ∑ i : Fin 4, (H i).card := sum_le_sum (fun i _ => (transfer i).1)
      _ = ((univ : Finset (Fin 4)).biUnion H).card := (card_biUnion hdisj).symm
      _ ≤ R.card := card_le_card hsub
  · have hcoef :
        (7 / 4 : ℚ) * (1 / 45045) ≤ ∑ i : Fin 4, (1 : ℚ) / ((B i + 1 : ℕ) : ℚ) := by
      norm_num [Fin.sum_univ_succ, B]
    have perTerm (t : ℕ) (ht : t ∈ L) :
        (7 / 4 : ℚ) * (1 / ((45045 * t : ℕ) : ℚ)) ≤
          ∑ i : Fin 4, (1 : ℚ) / ((B i * t + 1 : ℕ) : ℚ) := by
      have htpos := hl.trans_le (hT t (mem_filter.mp ht).1).1
      have htq : 0 < (t : ℚ) := by exact_mod_cast htpos
      calc
        (7 / 4 : ℚ) * (1 / ((45045 * t : ℕ) : ℚ)) =
            ((7 / 4 : ℚ) * (1 / 45045)) * (1 / (t : ℚ)) := by
          push_cast
          field_simp
        _ ≤ (∑ i : Fin 4, (1 : ℚ) / ((B i + 1 : ℕ) : ℚ)) * (1 / (t : ℚ)) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = ∑ i : Fin 4, (1 : ℚ) / ((((B i + 1) * t) : ℕ) : ℚ) := by
          rw [sum_mul]
          apply sum_congr rfl
          intro i _
          push_cast
          field_simp
        _ ≤ ∑ i : Fin 4, (1 : ℚ) / ((B i * t + 1 : ℕ) : ℚ) := by
          apply sum_le_sum
          intro i _
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast (show B i * t + 1 ≤ (B i + 1) * t by
            rw [Nat.add_mul, one_mul]
            omega)
    calc
      (7 / 4 : ℚ) * (∑ t ∈ L, (1 : ℚ) / ((45045 * t : ℕ) : ℚ)) =
          ∑ t ∈ L, (7 / 4 : ℚ) * (1 / ((45045 * t : ℕ) : ℚ)) := by rw [mul_sum]
      _ ≤ ∑ t ∈ L, ∑ i : Fin 4, (1 : ℚ) / ((B i * t + 1 : ℕ) : ℚ) :=
        sum_le_sum perTerm
      _ = ∑ i : Fin 4, ∑ t ∈ L, (1 : ℚ) / ((B i * t + 1 : ℕ) : ℚ) := sum_comm
      _ ≤ ∑ i : Fin 4, ∑ n ∈ H i, (1 : ℚ) / n := sum_le_sum (fun i _ => (transfer i).2)
      _ = ∑ n ∈ (univ : Finset (Fin 4)).biUnion H, (1 : ℚ) / n :=
        (sum_biUnion hdisj).symm
      _ ≤ ∑ n ∈ R, (1 : ℚ) / n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

