-- Prove2me | solution 1 for DeletedPrimes.window_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:16:42.686148+00:00
-- url     : https://prove2.me/submissions/80f70506-ce9f-4397-bf66-cf3632146ab0

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
import Theorems.Thm_DeletedPrimes_card_primes_dvd_le
import Theorems.Thm_DeletedPrimes_card_window_dvd_le

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (T : Fin k → Finset ℕ) (Y L : Fin k → ℕ)
    (hp : ∀ i, ∀ q ∈ T i, q.Prime) (hY : ∀ i, ∀ q ∈ T i, Y i ≤ q) (hY2 : ∀ i, 2 ≤ Y i)
    (n : ℤ) (J : ℕ) (hnJ : (J : ℤ) < |n|)
    (hL : ∀ i, ∀ j : ℤ, |j| ≤ J → (n + j).natAbs < Y i ^ (L i + 1)) (I : Finset (Fin k)) :
    ((Fintype.piFinset T).filter
        fun f : Fin k → ℕ => ∃ j : ℤ, j ≠ 0 ∧ |j| ≤ J ∧ ((∏ i, f i : ℕ) : ℤ) ∣ n + j).card
      ≤ (∏ i ∈ I, (T i).card) * (2 * J / ∏ i ∈ I, Y i + 1) * ∏ i ∈ Iᶜ, L i := by
  set YI := ∏ i ∈ I, Y i with hYI_def
  have hYI : 0 < YI := Finset.prod_pos (fun i _ => by have := hY2 i; omega)
  -- the `I`-parts
  set G : Finset (Fin k → ℕ) := Fintype.piFinset (fun i => if i ∈ I then T i else {0}) with hG_def
  -- admissible shifts for an `I`-part
  set JS : (Fin k → ℕ) → Finset ℤ := fun g =>
    (Finset.Icc (-(J : ℤ)) J).filter (fun j => ((∏ i ∈ I, g i : ℕ) : ℤ) ∣ n + j) with hJS_def
  -- the `Iᶜ`-parts compatible with a shift
  set H : ℤ → Finset (Fin k → ℕ) := fun j =>
    Fintype.piFinset (fun i => if i ∈ I then {0} else (T i).filter (fun p => (p : ℤ) ∣ n + j))
    with hH_def
  have hsub : ((Fintype.piFinset T).filter
        fun f : Fin k → ℕ => ∃ j : ℤ, j ≠ 0 ∧ |j| ≤ J ∧ ((∏ i, f i : ℕ) : ℤ) ∣ n + j) ⊆
      G.biUnion (fun g => (JS g).biUnion (fun j => (H j).image (fun h => g + h))) := by
    intro f hf
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
    obtain ⟨hfT, j, -, hj, hdvd⟩ := hf
    rw [Finset.mem_biUnion]
    refine ⟨fun i => if i ∈ I then f i else 0, ?_, ?_⟩
    · rw [hG_def, Fintype.mem_piFinset]
      intro i
      by_cases hi : i ∈ I <;> simp [hi, hfT i]
    rw [Finset.mem_biUnion]
    refine ⟨j, ?_, ?_⟩
    · rw [hJS_def]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨(abs_le.mp hj), ?_⟩
      have e : (∏ i ∈ I, (if i ∈ I then f i else 0)) = ∏ i ∈ I, f i :=
        Finset.prod_congr rfl (fun i hi => by simp [hi])
      rw [e]
      refine dvd_trans ?_ hdvd
      exact Int.natCast_dvd_natCast.mpr (Finset.prod_dvd_prod_of_subset I Finset.univ f
        (Finset.subset_univ I))
    rw [Finset.mem_image]
    refine ⟨fun i => if i ∈ I then 0 else f i, ?_, ?_⟩
    · rw [hH_def, Fintype.mem_piFinset]
      intro i
      by_cases hi : i ∈ I
      · simp [hi]
      · simp only [hi, ite_false, Finset.mem_filter]
        refine ⟨hfT i, dvd_trans ?_ hdvd⟩
        exact Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem f (Finset.mem_univ i))
    · funext i
      by_cases hi : i ∈ I <;> simp [hi]
  have hH : ∀ j : ℤ, |j| ≤ J → (H j).card ≤ ∏ i ∈ Iᶜ, L i := by
    intro j hj
    have hnj : n + j ≠ 0 := by
      intro h
      have : n = -j := by linarith
      rw [this, abs_neg] at hnJ
      linarith
    rw [hH_def]
    simp only
    rw [Fintype.card_piFinset, ← Finset.prod_mul_prod_compl I]
    have e1 : ∏ i ∈ I, (if i ∈ I then ({0} : Finset ℕ) else
        (T i).filter (fun p => (p : ℤ) ∣ n + j)).card = 1 :=
      Finset.prod_eq_one (fun i hi => by simp [hi])
    rw [e1, one_mul]
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i hi
    rw [Finset.mem_compl] at hi
    simp only [hi, ite_false]
    apply card_primes_dvd_le (hY2 i) hnj (hL i j hj)
    · intro p hp'; exact hp i p (Finset.mem_filter.mp hp').1
    · intro p hp'; exact hY i p (Finset.mem_filter.mp hp').1
    · intro p hp'; exact (Finset.mem_filter.mp hp').2
  have hJS : ∀ g ∈ G, (JS g).card ≤ 2 * J / YI + 1 := by
    intro g hg
    rw [hG_def, Fintype.mem_piFinset] at hg
    have hge : YI ≤ ∏ i ∈ I, g i := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      have := hg i
      simp only [hi, ite_true] at this
      exact hY i _ this
    calc (JS g).card ≤ 2 * J / (∏ i ∈ I, g i) + 1 :=
          card_window_dvd_le n J _ (lt_of_lt_of_le hYI hge)
      _ ≤ 2 * J / YI + 1 := by
          gcongr
  have hGcard : G.card = ∏ i ∈ I, (T i).card := by
    rw [hG_def, Fintype.card_piFinset, ← Finset.prod_mul_prod_compl I]
    have e1 : ∏ i ∈ Iᶜ, (if i ∈ I then T i else ({0} : Finset ℕ)).card = 1 :=
      Finset.prod_eq_one (fun i hi => by rw [Finset.mem_compl] at hi; simp [hi])
    rw [e1, mul_one]
    exact Finset.prod_congr rfl (fun i hi => by simp [hi])
  calc _ ≤ (G.biUnion (fun g => (JS g).biUnion (fun j => (H j).image (fun h => g + h)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ g ∈ G, ((JS g).biUnion (fun j => (H j).image (fun h => g + h))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ g ∈ G, ∑ j ∈ JS g, ((H j).image (fun h => g + h)).card :=
        Finset.sum_le_sum (fun g _ => Finset.card_biUnion_le)
    _ ≤ ∑ g ∈ G, ∑ j ∈ JS g, ∏ i ∈ Iᶜ, L i := by
        apply Finset.sum_le_sum
        intro g _
        apply Finset.sum_le_sum
        intro j hj
        rw [hJS_def] at hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        exact Finset.card_image_le.trans (hH j (abs_le.mpr hj.1))
    _ = ∑ g ∈ G, (JS g).card * ∏ i ∈ Iᶜ, L i := by
        simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ g ∈ G, (2 * J / YI + 1) * ∏ i ∈ Iᶜ, L i := by
        apply Finset.sum_le_sum
        intro g hg
        exact Nat.mul_le_mul_right _ (hJS g hg)
    _ = G.card * ((2 * J / YI + 1) * ∏ i ∈ Iᶜ, L i) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (∏ i ∈ I, (T i).card) * (2 * J / YI + 1) * ∏ i ∈ Iᶜ, L i := by
        rw [hGcard, mul_assoc]
end DeletedPrimes
