-- Prove2me | solution 1 for Erdos287.few_prime_layers_with_few_omissions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:20:07.115884+00:00
-- url     : https://prove2.me/submissions/e40ab483-e371-4dc6-9945-5ce7b1b8e163

import Mathlib
import Theorems.Thm_Erdos287_few_exceptional_primes_for_cofactor_subsets

open Finset

set_option autoImplicit false

private theorem scaled_sum (A : Finset ℕ) (L : ℕ)
    (hA : ∀ n ∈ A, 0 < n ∧ n ∣ L) :
    (L : ℚ) * (∑ n ∈ A, (1 : ℚ) / n) = ((∑ n ∈ A, L / n : ℕ) : ℚ) := by
  rw [mul_sum, Nat.cast_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [mul_one_div]
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (hA n hn).1.ne')).mpr
  exact_mod_cast (Nat.div_mul_cancel (hA n hn).2).symm

/-- Almost-full prime layers are exceptional. The bound counts the possible
cofactor intervals and the small sets deleted from those intervals. -/
theorem solution (D P : Finset ℕ) (m M B Y K R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hY : 2 ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ M / p ≤ B ∧
      R ≤ (Finset.Icc ((m - 1) / p + 1) (M / p)).card)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1)) :
    (P.filter (fun p =>
      ((Finset.Icc ((m - 1) / p + 1) (M / p)).filter (fun c => c * p ∉ D)).card < R)).card
      ≤ ((B + 1) * (B + 1)) * (∑ j ∈ Finset.range R, B.choose j) * K := by
  classical
  let U : Finset ℕ := Icc 1 B
  let L := U.lcm id
  let C (p : ℕ) := Icc ((m - 1) / p + 1) (M / p)
  let T (p : ℕ) := (C p).filter (fun c => c * p ∈ D)
  let A (p : ℕ) := (C p).filter (fun c => c * p ∉ D)
  let Q := P.filter (fun p => (A p).card < R)
  let I := Icc 1 (B + 1) ×ˢ range (B + 1)
  let J := (range R).biUnion (fun j => U.powersetCard j)
  let F := ((I ×ˢ J).image (fun z => Icc z.1.1 z.1.2 \ z.2)).filter Finset.Nonempty
  have hU (n : ℕ) (hn : n ∈ U) : 0 < n ∧ n ∣ L := ⟨(mem_Icc.mp hn).1, dvd_lcm hn⟩
  have hL : 0 < L := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun n hn => (hU n hn).1.ne'))
  have hC (p : ℕ) (hp : p ∈ P) : C p ⊆ U := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨(Nat.succ_le_succ (Nat.zero_le _)).trans hlo,
      hhi.trans (hP p hp).2.2.1⟩
  have hF (V : Finset ℕ) (hV : V ∈ F) : V ⊆ U ∧ V.Nonempty := by
    obtain ⟨hV, hn⟩ := mem_filter.mp hV
    obtain ⟨⟨⟨a, b⟩, S⟩, hz, rfl⟩ := mem_image.mp hV
    refine ⟨?_, hn⟩
    intro n hn
    obtain ⟨hn, _⟩ := mem_sdiff.mp hn
    have hlo : a ≤ n := (mem_Icc.mp hn).1
    have hhi : n ≤ b := (mem_Icc.mp hn).2
    have ha : 1 ≤ a := (mem_Icc.mp (mem_product.mp (mem_product.mp hz).1).1).1
    have hb : b < B + 1 := mem_range.mp (mem_product.mp (mem_product.mp hz).1).2
    exact mem_Icc.mpr ⟨ha.trans hlo, by omega⟩
  have hW (p : ℕ) (hp : p ∈ P) : p ∣ ∑ c ∈ T p, L / c := by
    have hpprime := (hP p hp).1
    let Dp := D.filter (fun n => p ∣ n)
    let V := D.filter (fun n => ¬ p ∣ n)
    let N := V.lcm id
    let W := ∑ c ∈ T p, L / c
    let Z := ∑ n ∈ V, N / n
    have hNV : ∀ n ∈ V, 0 < n ∧ n ∣ N := fun n hn =>
      ⟨hm.trans_le (mem_Icc.mp (hD (mem_filter.mp hn).1)).1, dvd_lcm hn⟩
    have hpN : ¬ p ∣ N := by
      intro h
      obtain ⟨n, hn, hpn⟩ := (hpprime.prime.dvd_finsetProd_iff id).mp
        (h.trans (V.lcm_dvd_prod id))
      exact (mem_filter.mp hn).2 hpn
    have hsplit := sum_filter_add_sum_filter_not D (fun n => p ∣ n) (fun n => (1 : ℚ) / n)
    change (∑ n ∈ Dp, (1 : ℚ) / n) + (∑ n ∈ V, (1 : ℚ) / n) = _ at hsplit
    rw [hsum] at hsplit
    have hImage : (T p).image (fun c => c * p) = Dp := by
      ext n
      constructor
      · rintro hn
        obtain ⟨c, hc, rfl⟩ := mem_image.mp hn
        exact mem_filter.mpr ⟨(mem_filter.mp hc).2, dvd_mul_left p c⟩
      · intro hn
        obtain ⟨hnD, hpn⟩ := mem_filter.mp hn
        obtain ⟨hlo, hhi⟩ := mem_Icc.mp (hD hnD)
        have he := Nat.div_mul_cancel hpn
        refine mem_image.mpr ⟨n / p, mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩, he⟩
        · apply Nat.succ_le_iff.mpr
          apply (Nat.div_lt_iff_lt_mul hpprime.pos).mpr
          omega
        · exact Nat.div_le_div_right hhi
        · rwa [he]
    have hScaleP :
        (p : ℚ) * (∑ n ∈ Dp, (1 : ℚ) / n) = ∑ c ∈ T p, (1 : ℚ) / c := by
      rw [← hImage, sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_right hpprime.pos he), mul_sum]
      refine sum_congr rfl fun c hc => ?_
      have hcp : (0 : ℚ) < c := by exact_mod_cast (hU c (hC p hp (mem_filter.mp hc).1)).1
      have hpp : (0 : ℚ) < p := by exact_mod_cast hpprime.pos
      push_cast
      field_simp
    have hScaleT := scaled_sum (T p) L (fun c hc => hU c (hC p hp (mem_filter.mp hc).1))
    have hScaleV := scaled_sum V N hNV
    have heq : N * W + p * L * Z = p * L * N := by
      have hq : (N : ℚ) * W + p * L * Z = p * L * N := by
        change (L : ℚ) * _ = (W : ℚ) at hScaleT
        change (N : ℚ) * _ = (Z : ℚ) at hScaleV
        linear_combination (p : ℚ) * L * N * hsplit - (L : ℚ) * N * hScaleP -
          (N : ℚ) * hScaleT - (p : ℚ) * L * hScaleV
      exact_mod_cast hq
    have hdiv : p ∣ N * W := by
      rw [show N * W = p * L * N - p * L * Z by omega]
      exact Nat.dvd_sub (by rw [mul_assoc]; exact dvd_mul_right p _)
        (by rw [mul_assoc]; exact dvd_mul_right p _)
    exact (hpprime.dvd_mul.mp hdiv).resolve_left hpN
  have hFcover (p : ℕ) (hp : p ∈ Q) : T p ∈ F := by
    obtain ⟨hpP, hpa⟩ := mem_filter.mp hp
    have hB : M / p ≤ B := (hP p hpP).2.2.1
    have hR : R ≤ (C p).card := (hP p hpP).2.2.2
    have hdiff : C p \ A p = T p := by
      ext n
      by_cases hn : n * p ∈ D <;> simp [A, T, hn]
    have ht : (T p).Nonempty := by
      have hsubs : A p ⊆ C p := filter_subset _ _
      have heq := card_sdiff_of_subset hsubs
      rw [hdiff] at heq
      exact card_pos.mp (by omega)
    have hpos : 1 ≤ (m - 1) / p + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hab : ((m - 1) / p + 1, M / p) ∈ I := by
      have h : (m - 1) / p ≤ M / p := Nat.div_le_div_right (by omega)
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨hpos, Nat.succ_le_succ (h.trans hB)⟩,
        mem_range.mpr (Nat.lt_succ_of_le hB)⟩
    have haj : A p ∈ J := mem_biUnion.mpr ⟨(A p).card, mem_range.mpr hpa,
      mem_powersetCard.mpr ⟨(filter_subset _ _).trans (hC p hpP), rfl⟩⟩
    exact mem_filter.mpr ⟨mem_image.mpr ⟨(_, A p), mem_product.mpr ⟨hab, haj⟩, hdiff⟩, ht⟩
  have hQ := Erdos287.few_exceptional_primes_for_cofactor_subsets U Q F L Y K hL hY hU hF
    (fun p hp => ⟨(hP p (mem_filter.mp hp).1).1, (hP p (mem_filter.mp hp).1).2.1⟩)
    (by simpa [U, L] using hbound)
    (fun p hp => ⟨T p, hFcover p hp, hW p (mem_filter.mp hp).1⟩)
  have hJ : J.card ≤ ∑ j ∈ range R, B.choose j := calc
    J.card ≤ ∑ j ∈ range R, (U.powersetCard j).card := card_biUnion_le
    _ = _ := by simp [U]
  have hFin : F.card ≤ ((B + 1) * (B + 1)) * (∑ j ∈ range R, B.choose j) := calc
    F.card ≤ (I ×ˢ J).card := card_filter_le _ _ |>.trans card_image_le
    _ = ((B + 1) * (B + 1)) * J.card := by simp [I]
    _ ≤ _ := Nat.mul_le_mul_left _ hJ
  exact hQ.trans (Nat.mul_le_mul_right _ hFin)

