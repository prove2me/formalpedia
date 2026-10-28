-- Prove2me | solution 1 for Erdos624.robust_half_measure_multicover_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:17:42.490604+00:00
-- url     : https://prove2.me/submissions/44230daa-e6fb-4923-8cb4-fde5047634dc

import Mathlib
open Finset

namespace E624R14C
open Finset

lemma avg {α ι : Type*} [DecidableEq α] (w : α → ℝ) (X : Finset α) (I : Finset ι)
    (B : ι → Finset α) :
    ∑ x ∈ X, w x * (#(I.filter (fun i => x ∈ B i)) : ℝ) =
      ∑ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x := by
  simp_rw [card_filter, Nat.cast_sum, mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

lemma step {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (X : Finset α)
    (I : Finset ι) (B : ι → Finset α) (x : α) (hx : x ∈ X)
    (hcov : ∀ S ⊆ X, #S ≤ s + 1 → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    ∀ S ⊆ X.erase x, #S ≤ s →
      lam ≤ #((I.filter (fun i => x ∈ B i)).filter (fun i => S ⊆ B i)) := by
  intro S hS hs
  have hxS : x ∉ S := fun h => by have := hS h; simp at this
  have := hcov (insert x S) (insert_subset hx (hS.trans (erase_subset _ _)))
    (by rw [card_insert_of_notMem hxS]; omega)
  convert this using 2
  ext i; simp [insert_subset_iff]; tauto

lemma sub_measure {α ι : Type*} [DecidableEq α] (w : α → ℝ) (X : Finset α)
    (B : ι → Finset α) (x : α) (hx : x ∈ X) (i : ι) (hi : x ∈ B i) :
    ∑ y ∈ (X.erase x).filter (fun y => y ∈ B i), w y =
      ∑ y ∈ X.filter (fun y => y ∈ B i), w y - w x := by
  have hm : x ∈ X.filter (fun y => y ∈ B i) := mem_filter.2 ⟨hx, hi⟩
  rw [← sum_erase_add _ _ hm, filter_erase]; ring

theorem strict {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam : ℕ) (hlam : 1 ≤ lam) :
    ∀ (s : ℕ) (X : Finset α) (I : Finset ι) (B : ι → Finset α),
      (∀ x ∈ X, 0 < w x) →
      (∀ i ∈ I, 2 * ∑ x ∈ X.filter (fun x => x ∈ B i), w x < ∑ x ∈ X, w x) →
      (∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) →
      (lam + 1) * 2 ^ s ≤ #I + 1 := by
  intro s
  induction s with
  | zero =>
    intro X I B _ _ hcov
    have := hcov ∅ (empty_subset _) (by simp)
    simp at this; simp; omega
  | succ s ih =>
    intro X I B hw hmeas hcov
    have hI : lam ≤ #I := by
      have := hcov ∅ (empty_subset _) (by simp); simpa using this
    have hXne : X.Nonempty := by
      by_contra hX
      rw [not_nonempty_iff_eq_empty] at hX
      obtain ⟨i, hi⟩ : I.Nonempty := card_pos.1 (by omega)
      have := hmeas i hi; simp [hX] at this
    have hW : 0 < ∑ x ∈ X, w x := sum_pos hw hXne
    have hd : ∀ x ∈ X, (lam + 1) * 2 ^ s ≤ #(I.filter (fun i => x ∈ B i)) + 1 := by
      intro x hx
      refine ih (X.erase x) _ B (fun y hy => hw y (mem_of_mem_erase hy)) ?_
        (step w lam s X I B x hx hcov)
      intro i hi
      rw [mem_filter] at hi
      rw [sub_measure w X B x hx i hi.2]
      have := hmeas i hi.1
      have e := sum_erase_add X w hx
      linarith [hw x hx]
    -- averaging
    set D : ℝ := ((lam + 1) * 2 ^ s : ℕ) - 1 with hD
    have h1 : D * ∑ x ∈ X, w x ≤ ∑ x ∈ X, w x * (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun x hx => ?_
      have := hd x hx
      have : D ≤ (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
        rw [hD]; have h' : ((lam + 1) * 2 ^ s : ℕ) ≤ (#(I.filter (fun i => x ∈ B i)) : ℝ) + 1 := by
          exact_mod_cast this
        linarith
      nlinarith [hw x hx]
    rw [avg] at h1
    have hIne : I.Nonempty := card_pos.1 (by omega)
    have h2 : 2 * ∑ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x < #I * ∑ x ∈ X, w x := by
      rw [mul_sum, ← nsmul_eq_mul, ← sum_const]
      exact sum_lt_sum_of_nonempty hIne fun i hi => hmeas i hi
    have h3 : 2 * D < #I := by
      by_contra hc; push Not at hc
      nlinarith
    have h4 : (((lam + 1) * 2 ^ (s + 1) : ℕ) : ℝ) < #I + 2 := by
      rw [hD] at h3; push_cast at h3 ⊢; rw [pow_succ]; linarith
    have h5 : (lam + 1) * 2 ^ (s + 1) < #I + 2 := by exact_mod_cast h4
    omega

theorem half {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (hlam : 1 ≤ lam)
    (hs : 1 ≤ s) (X : Finset α) (hX : X.Nonempty) (I : Finset ι) (B : ι → Finset α)
    (hw : ∀ x ∈ X, 0 < w x)
    (hmeas : ∀ i ∈ I, 2 * ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ ∑ x ∈ X, w x)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 2 := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hW : 0 < ∑ x ∈ X, w x := sum_pos hw hX
  have hd : ∀ x ∈ X, (lam + 1) * 2 ^ s ≤ #(I.filter (fun i => x ∈ B i)) + 1 := by
    intro x hx
    refine strict w lam hlam s (X.erase x) _ B (fun y hy => hw y (mem_of_mem_erase hy)) ?_
      (step w lam s X I B x hx hcov)
    intro i hi
    rw [mem_filter] at hi
    rw [sub_measure w X B x hx i hi.2]
    have := hmeas i hi.1
    have e := sum_erase_add X w hx
    linarith [hw x hx]
  set D : ℝ := ((lam + 1) * 2 ^ s : ℕ) - 1 with hD
  have h1 : D * ∑ x ∈ X, w x ≤ ∑ x ∈ X, w x * (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
    rw [mul_sum]
    refine sum_le_sum fun x hx => ?_
    have := hd x hx
    have : D ≤ (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
      rw [hD]; have h' : ((lam + 1) * 2 ^ s : ℕ) ≤ (#(I.filter (fun i => x ∈ B i)) : ℝ) + 1 := by
        exact_mod_cast this
      linarith
    nlinarith [hw x hx]
  rw [avg] at h1
  have h2 : 2 * ∑ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ #I * ∑ x ∈ X, w x := by
    rw [mul_sum, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => hmeas i hi
  have h3 : 2 * D ≤ #I := by
    by_contra hc; push Not at hc
    nlinarith
  have h4 : (((lam + 1) * 2 ^ (s + 1) : ℕ) : ℝ) ≤ #I + 2 := by
    rw [hD] at h3; push_cast at h3 ⊢; rw [pow_succ]; linarith
  exact_mod_cast h4
end E624R14C

namespace E624R15R
open Finset

theorem core {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (ε : ℝ)
    (hlam : 1 ≤ lam) (hs : 1 ≤ s) (X : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hw : ∀ x ∈ X, 0 < w x) (hsum : ∑ x ∈ X, w x = 1) (hε0 : 0 ≤ ε)
    (hε : 2 * ((lam : ℝ) + 1) ^ 2 * 4 ^ s * ε ≤ 1)
    (hmeas : ∀ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ 1 / 2 + ε)
    (hX : #X ≤ #I + 1)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  have h2r : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  set D : ℕ := (lam + 1) * 2 ^ r - 1 with hD
  have hD1 : 1 ≤ D := by
    have : 2 ≤ (lam + 1) * 2 ^ r := by nlinarith
    omega
  have hDe : (lam + 1) * 2 ^ (r + 1) = 2 * (D + 1) := by
    rw [pow_succ]; have : 1 ≤ (lam + 1) * 2 ^ r := by nlinarith
    rw [hD]; zify [this]; ring
  have ht : #I + 1 ≤ 2 * D := by omega
  -- heavy atoms have large degree
  have heavy : ∀ x ∈ X, 2 * ε < w x → D ≤ #(I.filter (fun i => x ∈ B i)) := by
    intro x hx hxw
    have := E624R14C.strict w lam hlam r (X.erase x) (I.filter (fun i => x ∈ B i)) B
      (fun y hy => hw y (mem_of_mem_erase hy)) ?_ (E624R14C.step w lam r X I B x hx hcov)
    · omega
    intro i hi
    rw [mem_filter] at hi
    rw [E624R14C.sub_measure w X B x hx i hi.2]
    have e := sum_erase_add X w hx
    have := hmeas i hi.1
    linarith
  have hpt : ∀ x ∈ X, (D : ℝ) * w x - D * (2 * ε) ≤
      w x * (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
    intro x hx
    have hD0 : (0 : ℝ) ≤ D := by positivity
    by_cases hh : 2 * ε < w x
    · have := heavy x hx hh
      have h' : (D : ℝ) ≤ #(I.filter (fun i => x ∈ B i)) := by exact_mod_cast this
      have := mul_le_mul_of_nonneg_left h' (hw x hx).le
      nlinarith
    · push_neg at hh
      have : (0 : ℝ) ≤ w x * (#(I.filter (fun i => x ∈ B i)) : ℝ) :=
        mul_nonneg (hw x hx).le (by positivity)
      nlinarith
  have hlow := sum_le_sum hpt
  rw [sum_sub_distrib, ← mul_sum, hsum, sum_const, nsmul_eq_mul, E624R14C.avg] at hlow
  have hup : ∑ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ #I * (1 / 2 + ε) := by
    have := sum_le_sum hmeas
    rwa [sum_const, nsmul_eq_mul] at this
  -- numeric contradiction
  have hXr : (#X : ℝ) ≤ #I + 1 := by exact_mod_cast hX
  have htr : (#I : ℝ) + 1 ≤ 2 * D := by exact_mod_cast ht
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hεD : 8 * ((D : ℝ) + 1) ^ 2 * ε ≤ 1 := by
    have : ((lam : ℝ) + 1) * 2 ^ (r + 1) = 2 * ((D : ℝ) + 1) := by exact_mod_cast hDe
    have h4 : (4 : ℝ) ^ (r + 1) = (2 ^ (r + 1)) ^ 2 := by
      rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
    rw [h4] at hε
    calc 8 * ((D : ℝ) + 1) ^ 2 * ε = 2 * (2 * ((D : ℝ) + 1)) ^ 2 * ε := by ring
      _ = 2 * (((lam : ℝ) + 1) * 2 ^ (r + 1)) ^ 2 * ε := by rw [this]
      _ = 2 * ((lam : ℝ) + 1) ^ 2 * (2 ^ (r + 1)) ^ 2 * ε := by ring
      _ ≤ 1 := hε
  have hI0 : (0 : ℝ) ≤ #I := by positivity
  -- D - 2εD|X| ≤ |I|(1/2+ε)
  have h1 : (D : ℝ) * ε * #X ≤ D * ε * (#I + 1) :=
    mul_le_mul_of_nonneg_left hXr (by positivity)
  have h2 : ε * (#I : ℝ) ≤ ε * (2 * D - 1) := mul_le_mul_of_nonneg_left (by linarith) hε0
  have h3 : (D : ℝ) * ε * (#I + 1) ≤ D * ε * (2 * D) :=
    mul_le_mul_of_nonneg_left htr (by positivity)
  -- 1/2 ≤ ε (|I| + 2D(|I|+1)) ≤ ε(4D²+2D-1) < ε·4(D+1)² ≤ 1/2
  have h5 : ε ≤ D * ε := by nlinarith
  rcases hε0.eq_or_lt with h0 | h0
  · subst h0
    simp only [mul_zero, sub_zero, add_zero, mul_one] at hlow hup
    linarith
  · nlinarith

theorem robust {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (ε : ℝ)
    (hlam : 1 ≤ lam) (hs : 1 ≤ s) (X : Finset α) (hX : X.Nonempty) (I : Finset ι)
    (B : ι → Finset α) (hw : ∀ x ∈ X, 0 < w x) (hε0 : 0 ≤ ε)
    (hε : 2 * ((lam : ℝ) + 1) ^ 2 * 4 ^ s * ε ≤ 1)
    (hmeas : ∀ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ (1 / 2 + ε) * ∑ x ∈ X, w x)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 2 := by
  classical
  set z : α → (I → ℝ) := fun x i => if x ∈ B i then 1 else 0 with hz
  have hW : 0 < ∑ x ∈ X, w x := sum_pos hw hX
  have hm : X.centerMass w z ∈ convexHull ℝ (z '' (X : Set α)) :=
    X.centerMass_mem_convexHull (fun x hx => (hw x hx).le) hW
      (fun x hx => Set.mem_image_of_mem z hx)
  obtain ⟨κ, hκ, z', c, hrange, hai, hcpos, hcsum, hcz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hm
  have hx' : ∀ j, ∃ x ∈ X, z x = z' j := fun j => by
    obtain ⟨x, hx, e⟩ := hrange ⟨j, rfl⟩; exact ⟨x, hx, e⟩
  choose xs hxsX hxsz using hx'
  have hinj : Function.Injective xs := fun a b h =>
    hai.injective (by rw [← hxsz a, ← hxsz b, h])
  have hcard : Fintype.card κ ≤ #I + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z'))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
    omega
  have key := core c lam s ε hlam hs (univ : Finset κ) I
    (fun i => univ.filter (fun j => xs j ∈ B i)) (fun j _ => hcpos j) hcsum hε0 hε ?_
    (by rw [card_univ]; exact hcard) ?_
  · exact key
  · intro i hi
    have e := congrFun hcz ⟨i, hi⟩
    rw [Finset.sum_apply] at e
    have lhs : ∑ j, (c j • z' j) ⟨i, hi⟩ =
        ∑ j ∈ univ.filter (fun j => j ∈ univ.filter (fun j => xs j ∈ B i)), c j := by
      rw [sum_filter]
      refine sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, ← hxsz j, hz, smul_eq_mul]
      simp only [mem_filter, mem_univ, true_and]
      by_cases h : xs j ∈ B i <;> simp [h]
    have rhs : X.centerMass w z ⟨i, hi⟩ =
        (∑ x ∈ X.filter (fun x => x ∈ B i), w x) / ∑ x ∈ X, w x := by
      rw [Finset.centerMass, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, sum_filter,
        div_eq_inv_mul]
      congr 1
      refine sum_congr rfl fun x _ => ?_
      rw [Pi.smul_apply, hz, smul_eq_mul]
      by_cases h : x ∈ B i <;> simp [h]
    rw [lhs, rhs] at e
    rw [e, div_le_iff₀ hW]
    exact hmeas i hi
  · intro S _ hS
    have := hcov (S.image xs) (fun x hx => by
        obtain ⟨j, -, rfl⟩ := mem_image.1 hx; exact hxsX j)
      (card_image_le.trans hS)
    refine this.trans (card_le_card fun i hi => ?_)
    simp only [mem_filter] at hi ⊢
    refine ⟨hi.1, fun j hj => ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    exact hi.2 (mem_image_of_mem xs hj)
end E624R15R

namespace Erdos624

theorem robust_half_measure_multicover_bound {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (ε : ℝ)
    (hlam : 1 ≤ lam) (hs : 1 ≤ s) (X : Finset α) (hX : X.Nonempty) (I : Finset ι)
    (B : ι → Finset α) (hw : ∀ x ∈ X, 0 < w x) (hε0 : 0 ≤ ε)
    (hε : 2 * ((lam : ℝ) + 1) ^ 2 * 4 ^ s * ε ≤ 1)
    (hmeas : ∀ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ (1 / 2 + ε) * ∑ x ∈ X, w x)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 2 := by
  exact E624R15R.robust w lam s ε hlam hs X hX I B hw hε0 hε hmeas hcov

end Erdos624

open Finset

theorem solution {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (ε : ℝ)
    (hlam : 1 ≤ lam) (hs : 1 ≤ s) (X : Finset α) (hX : X.Nonempty) (I : Finset ι)
    (B : ι → Finset α) (hw : ∀ x ∈ X, 0 < w x) (hε0 : 0 ≤ ε)
    (hε : 2 * ((lam : ℝ) + 1) ^ 2 * 4 ^ s * ε ≤ 1)
    (hmeas : ∀ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ (1 / 2 + ε) * ∑ x ∈ X, w x)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 2 :=
  Erdos624.robust_half_measure_multicover_bound w lam s ε hlam hs X hX I B hw hε0 hε hmeas hcov
