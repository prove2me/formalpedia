-- Prove2me | solution 1 for Erdos30.obryant_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T02:30:43.393987+00:00
-- url     : https://prove2.me/submissions/2b8baf61-2392-4c6d-8cb0-bb1f84abe862

import Mathlib
import Definitions.Def_Erdos30Basic

/-!
O'Bryant's bound `h N ≤ √N + 0.99703 N^{1/4}` for large `N` (K. O'Bryant, *On the size of finite
Sidon sets*, arXiv:2207.07800, §3.2), with re-optimised rational parameters.

Outline. For a Sidon set `A ⊆ [lo, lo + D]` of size `k` and window length `T`, double counting the
window counts `W j = #(A ∩ [j - T, j))` gives the exact Erdős–Turán identity; we use it as the
inequality `core`: `(kT)² + M·V + 2M·S ≤ M (kT + T(T-1))` (`M = D + T`), where `V` is a partial
variance of the window counts and `S` sums `T - r` over differences `r` known to be missing.
With `T ≈ τ k^{3/2}` either the end windows have large variance (case A, `realA`), or the ends are
dense: then the small differences inside the two end clusters are missing from the middle set,
whose diameter is then large (case B, `S_lb`, `M_lb`, `realB_final`). Both cases give
`D ≥ k² - 1.99405 k^{3/2}` once `√k ≥ 10^7` (`diam_bound`); inverting gives the bound.
-/


set_option linter.all false

open Finset

namespace Erdos30
namespace OB

/-- Ordered pairs `a < b` of elements of `X`. -/
def prs (X : Finset ℕ) : Finset (ℕ × ℕ) := (X ×ˢ X).filter (fun p => p.1 < p.2)

/-- Window counts: `W B T j = #{a ∈ B : a < j ≤ a + T}`. -/
def W (B : Finset ℕ) (T j : ℕ) : ℕ := (B.filter (fun a => a < j ∧ j ≤ a + T)).card

lemma sum_prod_symm (X : Finset ℕ) (g : ℕ → ℕ → ℕ) (hg : ∀ a b, g a b = g b a) :
    ∑ p ∈ X ×ˢ X, g p.1 p.2 = ∑ a ∈ X, g a a + 2 * ∑ p ∈ prs X, g p.1 p.2 := by
  rw [← sum_filter_add_sum_filter_not (X ×ˢ X) (fun p => p.1 < p.2)]
  rw [← sum_filter_add_sum_filter_not ((X ×ˢ X).filter (fun p => ¬ p.1 < p.2))
    (fun p => p.1 = p.2)]
  have h3 : ∑ p ∈ ((X ×ˢ X).filter (fun p => ¬ p.1 < p.2)).filter (fun p => p.1 = p.2),
      g p.1 p.2 = ∑ a ∈ X, g a a := by
    apply sum_nbij' (fun p => p.1) (fun a => (a, a))
    · intro p hp; simp only [mem_filter, mem_product] at hp; exact hp.1.1.1
    · intro a ha; simp [ha]
    · intro p hp; simp only [mem_filter, mem_product] at hp
      ext <;> simp [hp.2]
    · intro a _; rfl
    · intro p hp; simp only [mem_filter, mem_product] at hp; rw [hp.2]
  have h4 : ∑ p ∈ ((X ×ˢ X).filter (fun p => ¬ p.1 < p.2)).filter (fun p => ¬ p.1 = p.2),
      g p.1 p.2 = ∑ p ∈ prs X, g p.1 p.2 := by
    apply sum_nbij' Prod.swap Prod.swap
    · intro p hp; rw [mem_filter, mem_filter, mem_product] at hp
      rw [prs, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hp.1.1.2, hp.1.1.1⟩, by omega⟩
    · intro p hp; rw [prs, mem_filter, mem_product] at hp
      rw [mem_filter, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨⟨hp.1.2, hp.1.1⟩, by omega⟩, by omega⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp [hg]
  rw [h3, h4]; unfold prs; ring

lemma sum_W (B : Finset ℕ) (lo D T : ℕ) (hB : ∀ a ∈ B, lo ≤ a ∧ a ≤ lo + D) :
    ∑ j ∈ Icc (lo + 1) (lo + D + T), W B T j = B.card * T := by
  unfold W
  simp_rw [card_filter]
  rw [sum_comm, card_eq_sum_ones, sum_mul]
  apply sum_congr rfl
  intro a ha
  obtain ⟨h1, h2⟩ := hB a ha
  rw [← card_filter, one_mul]
  have : (Icc (lo + 1) (lo + D + T)).filter (fun j => a < j ∧ j ≤ a + T) = Ioc a (a + T) := by
    ext j; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  rw [this, Nat.card_Ioc]; omega

lemma sum_W_sq (B : Finset ℕ) (lo D T : ℕ) (hB : ∀ a ∈ B, lo ≤ a ∧ a ≤ lo + D) :
    ∑ j ∈ Icc (lo + 1) (lo + D + T), (W B T j) ^ 2
      = B.card * T + 2 * ∑ p ∈ prs B, (T - (p.2 - p.1)) := by
  have hsq : ∀ j, (W B T j) ^ 2 = ∑ p ∈ B ×ˢ B,
      if (p.1 < j ∧ j ≤ p.1 + T) ∧ (p.2 < j ∧ j ≤ p.2 + T) then 1 else 0 := by
    intro j
    unfold W
    rw [sq, ← card_product, ← filter_product, card_filter]
  simp_rw [hsq]
  rw [sum_comm]
  have hg : ∀ p ∈ B ×ˢ B, (∑ j ∈ Icc (lo + 1) (lo + D + T),
      if (p.1 < j ∧ j ≤ p.1 + T) ∧ (p.2 < j ∧ j ≤ p.2 + T) then 1 else 0)
      = min p.1 p.2 + T - max p.1 p.2 := by
    intro p hp
    simp only [mem_product] at hp
    obtain ⟨h1, h2⟩ := hB _ hp.1
    obtain ⟨h3, h4⟩ := hB _ hp.2
    rw [← card_filter]
    have : (Icc (lo + 1) (lo + D + T)).filter
        (fun j => (p.1 < j ∧ j ≤ p.1 + T) ∧ (p.2 < j ∧ j ≤ p.2 + T))
        = Ioc (max p.1 p.2) (min p.1 p.2 + T) := by
      ext j; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
    rw [this, Nat.card_Ioc]
  rw [sum_congr rfl hg]
  rw [sum_prod_symm B (fun a b => min a b + T - max a b)
    (fun a b => by rw [min_comm, max_comm])]
  congr 1
  · rw [card_eq_sum_ones, sum_mul]; simp
  · congr 1
    apply sum_congr rfl
    intro p hp
    simp only [prs, mem_filter] at hp
    rw [min_eq_left hp.2.le, max_eq_right hp.2.le]
    omega

/-- Gauss-type sum: `2 Σ_{r ∈ (range T).erase 0} (T - r) = T (T - 1)`. -/
lemma two_sum_erase (T : ℕ) : 2 * ∑ r ∈ (range T).erase 0, (T - r) = T * (T - 1) := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have h0 : (0 : ℕ) ∈ range T := mem_range.2 hT
  have h1 := add_sum_erase (range T) (fun r => T - r) h0
  have h2 : ∑ r ∈ range T, (T - r) = ∑ r ∈ range T, (r + 1) := by
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro j hj; rw [mem_range] at hj; omega
  have h3 : ∑ r ∈ range T, (r + 1) = ∑ r ∈ range T, r + T := by
    rw [sum_add_distrib]; simp
  have h4 := sum_range_id_mul_two T
  have : ∑ r ∈ (range T).erase 0, (T - r) + T = ∑ r ∈ range T, r + T := by
    rw [← h3, ← h2, ← h1]; omega
  have h5 : ∑ r ∈ (range T).erase 0, (T - r) = ∑ r ∈ range T, r := by omega
  rw [h5]; linarith

lemma sidon_diff_inj (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (p q : ℕ × ℕ)
    (hp : p ∈ prs A) (hq : q ∈ prs A) (h : p.2 - p.1 = q.2 - q.1) : p = q := by
  simp only [prs, mem_filter, mem_product] at hp hq
  have hs : p.1 + q.2 = q.1 + p.2 := by omega
  rcases hA p.1 hp.1.1 q.1 hq.1.1 q.2 hq.1.2 p.2 hp.1.2 hs with h1 | h1
  · ext
    · exact h1.1
    · exact h1.2.symm
  · omega

lemma prs_mono {X Y : Finset ℕ} (h : X ⊆ Y) : prs X ⊆ prs Y := by
  intro p hp; simp only [prs, mem_filter, mem_product] at hp ⊢
  exact ⟨⟨h hp.1.1, h hp.1.2⟩, hp.2⟩

lemma prs_disj {X Y : Finset ℕ} (h : Disjoint X Y) : Disjoint (prs X) (prs Y) := by
  rw [disjoint_left]; intro p hp hq
  simp only [prs, mem_filter, mem_product] at hp hq
  exact disjoint_left.1 h hp.1.1 hq.1.1

lemma prs_bound (A X1 X2 X3 : Finset ℕ) (hA : IsSidon (A : Set ℕ))
    (h1 : X1 ⊆ A) (h2 : X2 ⊆ A) (h3 : X3 ⊆ A)
    (d12 : Disjoint X1 X2) (d13 : Disjoint X1 X3) (d23 : Disjoint X2 X3) (T : ℕ) :
    2 * (∑ p ∈ prs X1, (T - (p.2 - p.1)) + ∑ p ∈ prs X2, (T - (p.2 - p.1))
      + ∑ p ∈ prs X3, (T - (p.2 - p.1))) ≤ T * (T - 1) := by
  rw [← sum_union (prs_disj d12), ← sum_union]
  swap
  · rw [disjoint_union_left]; exact ⟨prs_disj d13, prs_disj d23⟩
  set P := prs X1 ∪ prs X2 ∪ prs X3 with hP
  have hPA : P ⊆ prs A := by
    rw [hP]
    exact union_subset (union_subset (prs_mono h1) (prs_mono h2)) (prs_mono h3)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) P := by
    intro p hp q hq h
    exact sidon_diff_inj A hA p q (hPA hp) (hPA hq) h
  rw [← sum_image (f := fun r => T - r) hinj]
  rw [← sum_filter_of_ne (p := fun r => r < T)]
  swap
  · intro r _ hr; omega
  rw [← two_sum_erase T]
  apply Nat.mul_le_mul_left
  apply sum_le_sum_of_subset
  intro r hr
  simp only [mem_filter, mem_image] at hr
  obtain ⟨⟨p, hp, rfl⟩, hlt⟩ := hr
  have := hPA hp
  simp only [prs, mem_filter] at this
  simp only [mem_erase, mem_range]
  omega

/-- The core inequality (Erdős–Turán with variance and missing-difference terms). -/
theorem core (A B X2 X3 : Finset ℕ) (hA : IsSidon (A : Set ℕ))
    (hB : B ⊆ A) (h2 : X2 ⊆ A) (h3 : X3 ⊆ A)
    (d12 : Disjoint B X2) (d13 : Disjoint B X3) (d23 : Disjoint X2 X3)
    (lo D T : ℕ) (hT : 1 ≤ T) (hBr : ∀ a ∈ B, lo ≤ a ∧ a ≤ lo + D)
    (J' : Finset ℕ) (hJ : J' ⊆ Icc (lo + 1) (lo + D + T)) :
    ((B.card : ℝ) * T) ^ 2
      + ((D : ℝ) + T) * ∑ j ∈ J', ((W B T j : ℝ) - (B.card : ℝ) * T / ((D : ℝ) + T)) ^ 2
      + 2 * ((D : ℝ) + T) * ((∑ p ∈ prs X2, ((T - (p.2 - p.1) : ℕ) : ℝ))
          + ∑ p ∈ prs X3, ((T - (p.2 - p.1) : ℕ) : ℝ))
      ≤ ((D : ℝ) + T) * ((B.card : ℝ) * T + (T : ℝ) * ((T : ℝ) - 1)) := by
  have hs1 := sum_W B lo D T hBr
  have hs2 := sum_W_sq B lo D T hBr
  set J := Icc (lo + 1) (lo + D + T)
  have hJc : (J.card : ℝ) = (D : ℝ) + T := by
    simp only [J, Nat.card_Icc]; push_cast [show lo + D + T + 1 - (lo + 1) = D + T by omega]
    ring
  have hpb := prs_bound A B X2 X3 hA hB h2 h3 d12 d13 d23 T
  have hM : (0 : ℝ) < (D : ℝ) + T := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    positivity
  set M : ℝ := (D : ℝ) + T
  set k : ℝ := (B.card : ℝ)
  set Ab := k * T / M
  have hAbM : Ab * M = k * T := by simp only [Ab]; field_simp
  -- real versions
  have r1 : ∑ j ∈ J, (W B T j : ℝ) = k * T := by
    rw [← Nat.cast_sum, hs1]; push_cast; rfl
  have r2 : ∑ j ∈ J, (W B T j : ℝ) ^ 2
      = k * T + 2 * ∑ p ∈ prs B, ((T - (p.2 - p.1) : ℕ) : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hs2
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at this
    rw [this]
  have r3 : 2 * (∑ p ∈ prs B, ((T - (p.2 - p.1) : ℕ) : ℝ)
      + ∑ p ∈ prs X2, ((T - (p.2 - p.1) : ℕ) : ℝ)
      + ∑ p ∈ prs X3, ((T - (p.2 - p.1) : ℕ) : ℝ)) ≤ (T : ℝ) * ((T : ℝ) - 1) := by
    have : ((T * (T - 1) : ℕ) : ℝ) = (T : ℝ) * ((T : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos T with h | h
      · omega
      · push_cast [Nat.cast_sub h]; ring
    rw [← this]; exact_mod_cast hpb
  have hvar : ∑ j ∈ J, ((W B T j : ℝ) - Ab) ^ 2
      = ∑ j ∈ J, (W B T j : ℝ) ^ 2 - 2 * Ab * ∑ j ∈ J, (W B T j : ℝ) + J.card * Ab ^ 2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_sum]
    apply congrArg₂ _ (congrArg₂ _ rfl (sum_congr rfl fun _ _ => by ring)) rfl
  have hsub : ∑ j ∈ J', ((W B T j : ℝ) - Ab) ^ 2 ≤ ∑ j ∈ J, ((W B T j : ℝ) - Ab) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hJ (fun _ _ _ => sq_nonneg _)
  rw [hvar, r1, r2, hJc] at hsub
  have key : M * (2 * Ab * (k * T)) - M * (M * Ab ^ 2) = (k * T) ^ 2 := by
    have h0 : M * Ab = k * T := by rw [mul_comm]; exact hAbM
    have : M * (2 * Ab * (k * T)) - M * (M * Ab ^ 2) = 2 * (M * Ab) * (k * T) - (M * Ab) ^ 2 := by
      ring
    rw [this, h0]; ring
  have f1 := mul_le_mul_of_nonneg_left hsub hM.le
  have f2 := mul_le_mul_of_nonneg_left r3 hM.le
  linear_combination f1 + f2 - key

end OB
end Erdos30


set_option linter.all false

namespace Erdos30
namespace OB

/-- `Q t = t (t - 2) / 4`, a lower bound for `C(a,2) + C(b,2)` when `a + b = t`. -/
noncomputable def Qf (t : ℝ) : ℝ := t * (t - 2) / 4

lemma Qf_mono {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) : Qf s ≤ Qf t := by
  unfold Qf
  have e : t * (t - 2) - s * (s - 2) = (t - s) * (t + s - 2) := by ring
  have := mul_nonneg (sub_nonneg.2 hst) (by linarith : (0:ℝ) ≤ t + s - 2)
  linarith

/-- Lower bound for the missing-difference sum `S`. Here `c₁ = 2(1-α)a`, `c₂ = 2(1-αβ)a`. -/
lemma S_lb (a α β T2 X Y m1 m2 l l1 l2 S : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (ha : 0 ≤ a)
    (hm1 : 0 ≤ m1) (hm12 : m1 ≤ m2) (hm2 : m2 ≤ T2) (hm1Y : m1 ≤ Y) (hm2X : m2 - m1 ≤ X)
    (hl : 2 * (1 - α * β) * a - 2 ≤ l) (hl1 : 2 * (1 - α) * a - 2 ≤ l1)
    (hl2 : 2 * (1 - α * β) * a - 2 - 2 * (1 - α) * a ≤ l2)
    (h1 : 1 ≤ 2 * (1 - α) * a - 2) (h2 : 1 ≤ 2 * (1 - α * β) * a - 2 - 2 * (1 - α) * a)
    (hS : (T2 - m2) * Qf l + (m2 - m1) * Qf l1 + m1 * Qf l2 ≤ S) :
    T2 * ((1 - α * β) ^ 2 * a ^ 2 - 3 * (1 - α * β) * a)
      - a ^ 2 * (((1 - α * β) ^ 2 - (1 - α) ^ 2) * X
        + ((1 - α * β) ^ 2 - (α * (1 - β)) ^ 2) * Y) ≤ S := by
  have hab : α * β < α := mul_lt_of_lt_one_right hα hβ1
  have hc12 : 2 * (1 - α) * a - 2 ≤ 2 * (1 - α * β) * a - 2 := by
    have := mul_le_mul_of_nonneg_right hab.le ha; linarith
  have r1 : Qf (2 * (1 - α * β) * a - 2) ≤ Qf l :=
    Qf_mono (le_trans h1 hc12) hl
  have r2 : Qf (2 * (1 - α) * a - 2) ≤ Qf l1 := Qf_mono h1 hl1
  have r3 : Qf (2 * (1 - α * β) * a - 2 - 2 * (1 - α) * a) ≤ Qf l2 := Qf_mono h2 hl2
  have e1 : (T2 - m2) * Qf (2 * (1 - α * β) * a - 2) ≤ (T2 - m2) * Qf l :=
    mul_le_mul_of_nonneg_left r1 (by linarith)
  have e2 : (m2 - m1) * Qf (2 * (1 - α) * a - 2) ≤ (m2 - m1) * Qf l1 :=
    mul_le_mul_of_nonneg_left r2 (by linarith)
  have e3 : m1 * Qf (2 * (1 - α * β) * a - 2 - 2 * (1 - α) * a) ≤ m1 * Qf l2 :=
    mul_le_mul_of_nonneg_left r3 hm1
  set q2 := Qf (2 * (1 - α * β) * a - 2) with hq2
  set q1 := Qf (2 * (1 - α) * a - 2) with hq1
  set q12 := Qf (2 * (1 - α * β) * a - 2 - 2 * (1 - α) * a) with hq12
  have dX : q2 - q1 ≤ a ^ 2 * ((1 - α * β) ^ 2 - (1 - α) ^ 2) := by
    have : q2 - q1 = a ^ 2 * ((1 - α * β) ^ 2 - (1 - α) ^ 2) - 3 * (α - α * β) * a := by
      rw [hq1, hq2]; unfold Qf; ring
    rw [this]; have := mul_nonneg (by linarith : (0:ℝ) ≤ α - α * β) ha; linarith
  have dY : q2 - q12 ≤ a ^ 2 * ((1 - α * β) ^ 2 - (α * (1 - β)) ^ 2) := by
    have : q2 - q12 = a ^ 2 * ((1 - α * β) ^ 2 - (α * (1 - β)) ^ 2) - 3 * (1 - α) * a := by
      rw [hq12, hq2]; unfold Qf; ring
    rw [this]; have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α) ha; linarith
  have hq2' : q2 = (1 - α * β) ^ 2 * a ^ 2 - 3 * (1 - α * β) * a + 2 := by
    rw [hq2]; unfold Qf; ring
  have hαβ0 : 0 ≤ α * β := by positivity
  have hcX : 0 ≤ a ^ 2 * ((1 - α * β) ^ 2 - (1 - α) ^ 2) := by
    apply mul_nonneg (sq_nonneg a)
    have e : (1 - α * β) ^ 2 - (1 - α) ^ 2 = (α - α * β) * (2 - α - α * β) := by ring
    rw [e]; apply mul_nonneg <;> linarith
  have hcY : 0 ≤ a ^ 2 * ((1 - α * β) ^ 2 - (α * (1 - β)) ^ 2) := by
    apply mul_nonneg (sq_nonneg a)
    have e : (1 - α * β) ^ 2 - (α * (1 - β)) ^ 2 = (1 - α) * (1 + α - 2 * (α * β)) := by ring
    rw [e]; apply mul_nonneg <;> linarith
  have f1 := mul_le_mul_of_nonneg_left dX (by linarith : (0:ℝ) ≤ m2 - m1)
  have f2 := mul_le_mul_of_nonneg_left dY hm1
  have f3 := mul_le_mul_of_nonneg_right hm2X hcX
  have f4 := mul_le_mul_of_nonneg_right hm1Y hcY
  have hT2 : 0 ≤ T2 := by linarith
  have g : (T2 - m2) * q2 + (m2 - m1) * q1 + m1 * q12
      = T2 * q2 - (m2 - m1) * (q2 - q1) - m1 * (q2 - q12) := by ring
  have g2 : T2 * ((1 - α * β) ^ 2 * a ^ 2 - 3 * (1 - α * β) * a) ≤ T2 * q2 := by
    rw [hq2']; exact mul_le_mul_of_nonneg_left (by linarith) hT2
  linarith

/-- From the core inequality for the middle set: a lower bound for `M'`. -/
lemma M_lb (M' T2 k S : ℝ) (hM : 0 < M') (hT2 : 0 < T2)
    (h : (k * T2) ^ 2 + 2 * M' * S ≤ M' * (k * T2 + T2 * (T2 - 1))) :
    k ^ 2 * (1 - (k - 1) / T2 + 2 * S / T2 ^ 2) ≤ M' := by
  set Q := T2 * (k + T2 - 1) - 2 * S with hQ
  have h1 : k ^ 2 * T2 ^ 2 ≤ M' * Q := by
    have e : M' * Q = M' * (k * T2 + T2 * (T2 - 1)) - 2 * M' * S := by rw [hQ]; ring
    have e2 : k ^ 2 * T2 ^ 2 = (k * T2) ^ 2 := by ring
    rw [e, e2]; linarith
  have e : k ^ 2 * (1 - (k - 1) / T2 + 2 * S / T2 ^ 2) = k ^ 2 * (2 * T2 ^ 2 - Q) / T2 ^ 2 := by
    rw [hQ]; field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  rcases le_or_gt Q 0 with hq | hq
  · have : k ^ 2 * T2 ^ 2 ≤ 0 := le_trans h1 (mul_nonpos_of_nonneg_of_nonpos hM.le hq)
    have hk : k ^ 2 = 0 := by
      have h0 : k ^ 2 ≤ 0 := by
        by_contra hc; push_neg at hc
        have := mul_pos hc (pow_pos hT2 2); linarith
      exact le_antisymm h0 (sq_nonneg k)
    rw [hk]; simp; positivity
  · -- k² (2p - Q) Q ≤ k² p² ≤ M' Q p
    have hp : 0 < T2 ^ 2 := by positivity
    have amgm : (2 * T2 ^ 2 - Q) * Q ≤ T2 ^ 2 * T2 ^ 2 := by
      have e : T2 ^ 2 * T2 ^ 2 - (2 * T2 ^ 2 - Q) * Q = (T2 ^ 2 - Q) ^ 2 := by ring
      linarith [sq_nonneg (T2 ^ 2 - Q)]
    have : k ^ 2 * (2 * T2 ^ 2 - Q) * Q ≤ M' * T2 ^ 2 * Q := by
      have f1 := mul_le_mul_of_nonneg_left amgm (sq_nonneg k)
      have f2 := mul_le_mul_of_nonneg_right h1 hp.le
      calc k ^ 2 * (2 * T2 ^ 2 - Q) * Q = k ^ 2 * ((2 * T2 ^ 2 - Q) * Q) := by ring
        _ ≤ k ^ 2 * (T2 ^ 2 * T2 ^ 2) := f1
        _ = k ^ 2 * T2 ^ 2 * T2 ^ 2 := by ring
        _ ≤ M' * Q * T2 ^ 2 := f2
        _ = M' * T2 ^ 2 * Q := by ring
    exact le_of_mul_le_mul_right this hq

/-- Asymptotic assembly for the second case (all numerics abstracted into hypotheses). -/
lemma realB_final (P T a X Y z k D S τ τ₂ β δ Λ κ2 cX cY Khi κ ρ : ℝ)
    (hτ : 0 < τ) (hτ₂ : 0 < τ₂) (hβ : 0 < β) (hκ2 : 0 < κ2) (hP : 1 ≤ P)
    (hT1 : τ * P ^ 3 ≤ T) (hT2 : T ≤ τ * P ^ 3 + 125)
    (ha1 : τ * P ≤ a) (ha2 : a ≤ τ * P + 2) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXY : Y + β ^ 2 * X ≤ β ^ 2 * δ * T) (hz : T - X - Y ≤ z)
    (hκ : 0 ≤ κ) (hk1 : κ ≤ k) (hk2 : k ≤ P ^ 2)
    (hcX : 0 ≤ cX) (hcY : 0 ≤ cY)
    (hS : τ₂ * T * (κ2 ^ 2 * a ^ 2 - 3 * κ2 * a) - a ^ 2 * (cX * X + cY * Y) ≤ S)
    (hM : k ^ 2 * (1 - (k - 1) / (τ₂ * T) + 2 * S / (τ₂ * T) ^ 2) ≤ D - 2 * z + τ₂ * T)
    (hKhi : 2 * P ^ 4 * (τ * P + 2) ^ 2 ≤ Khi * (τ₂ ^ 2 * τ ^ 2 * P ^ 6))
    (hΛ1 : 2 + Khi * cX ≤ Λ) (hΛ2 : β ^ 2 * (2 + Khi * cY) ≤ Λ)
    (hco : 0 ≤ 2 - Λ * δ - τ₂) (h3 : 3 ≤ κ2 * τ * P)
    (hpoly : ρ ≤ (2 - Λ * δ - τ₂) * τ * P ^ 3 + κ ^ 2 - P ^ 3 / (τ * τ₂)
      + 2 * κ ^ 2 * (κ2 ^ 2 * τ ^ 2 * P ^ 2 - 3 * κ2 * τ * P) / (τ₂ * (τ * P ^ 3 + 125))) :
    ρ ≤ D := by
  have hP0 : 0 < P := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT1
  set T2 := τ₂ * T with hT2def
  have hT2pos : 0 < T2 := by positivity
  have hT2lo : τ₂ * τ * P ^ 3 ≤ T2 := by
    rw [hT2def, show τ₂ * τ * P ^ 3 = τ₂ * (τ * P ^ 3) by ring]
    exact mul_le_mul_of_nonneg_left hT1 hτ₂.le
  have hk0 : 0 ≤ k := le_trans hκ hk1
  have hσ : 0 ≤ cX * X + cY * Y := by positivity
  -- expand hM
  have eM : k ^ 2 * (1 - (k - 1) / T2 + 2 * S / T2 ^ 2)
      = k ^ 2 - k ^ 2 * (k - 1) / T2 + 2 * k ^ 2 * S / T2 ^ 2 := by
    field_simp
  rw [eM] at hM
  -- step c
  have sc : k ^ 2 * (k - 1) / T2 ≤ P ^ 3 / (τ * τ₂) := by
    rw [div_le_div_iff₀ hT2pos (by positivity)]
    have e1 : k ^ 2 * (k - 1) ≤ (P ^ 2) ^ 3 := by
      have : k ^ 3 ≤ (P ^ 2) ^ 3 := pow_le_pow_left₀ hk0 hk2 3
      have e : k ^ 2 * (k - 1) = k ^ 3 - k ^ 2 := by ring
      rw [e]; linarith [sq_nonneg k]
    calc k ^ 2 * (k - 1) * (τ * τ₂) ≤ (P ^ 2) ^ 3 * (τ * τ₂) :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
      _ = P ^ 3 * (τ₂ * τ * P ^ 3) := by ring
      _ ≤ P ^ 3 * T2 := mul_le_mul_of_nonneg_left hT2lo (by positivity)
  -- step d: K ≤ Khi
  have hKhi0 : 0 ≤ Khi := by
    have h0 : 0 ≤ 2 * P ^ 4 * (τ * P + 2) ^ 2 := by positivity
    have hpos : 0 < τ₂ ^ 2 * τ ^ 2 * P ^ 6 := by positivity
    exact (mul_nonneg_iff_of_pos_right hpos).1 (le_trans h0 hKhi)
  have hK : 2 * k ^ 2 * a ^ 2 / T2 ^ 2 ≤ Khi := by
    rw [div_le_iff₀ (by positivity)]
    have ha0 : 0 ≤ a := le_trans (by positivity) ha1
    have e1 : k ^ 2 ≤ P ^ 4 := by
      calc k ^ 2 ≤ (P ^ 2) ^ 2 := pow_le_pow_left₀ hk0 hk2 2
        _ = P ^ 4 := by ring
    have e2 : a ^ 2 ≤ (τ * P + 2) ^ 2 := pow_le_pow_left₀ ha0 ha2 2
    have e3 : (τ₂ * τ * P ^ 3) ^ 2 ≤ T2 ^ 2 := pow_le_pow_left₀ (by positivity) hT2lo 2
    calc 2 * k ^ 2 * a ^ 2 = 2 * (k ^ 2 * a ^ 2) := by ring
      _ ≤ 2 * (P ^ 4 * (τ * P + 2) ^ 2) := by
          have := mul_le_mul e1 e2 (sq_nonneg a) (by positivity); linarith
      _ = 2 * P ^ 4 * (τ * P + 2) ^ 2 := by ring
      _ ≤ Khi * (τ₂ ^ 2 * τ ^ 2 * P ^ 6) := hKhi
      _ = Khi * (τ₂ * τ * P ^ 3) ^ 2 := by ring
      _ ≤ Khi * T2 ^ 2 := mul_le_mul_of_nonneg_left e3 hKhi0
  -- step e
  have se : 2 * (X + Y) + Khi * (cX * X + cY * Y) ≤ Λ * δ * T := by
    have hb2 : 0 < β ^ 2 := by positivity
    have e1 : (2 + Khi * cX) * X ≤ Λ * X := mul_le_mul_of_nonneg_right hΛ1 hX
    have e2 : β ^ 2 * ((2 + Khi * cY) * Y) ≤ Λ * Y := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hΛ2 hY
    have e3 : (2 + Khi * cY) * Y ≤ Λ * Y / β ^ 2 := by rw [le_div_iff₀ hb2]; linarith
    have e4 : Λ * (X + Y / β ^ 2) ≤ Λ * (δ * T) := by
      have hΛ0 : 0 ≤ Λ := by
        have : 0 ≤ Khi * cY := mul_nonneg hKhi0 hcY
        have : 0 ≤ β ^ 2 * (2 + Khi * cY) := mul_nonneg (sq_nonneg β) (by linarith)
        linarith
      apply mul_le_mul_of_nonneg_left _ hΛ0
      rw [← sub_nonneg]
      have : δ * T - (X + Y / β ^ 2) = (β ^ 2 * δ * T - (Y + β ^ 2 * X)) / β ^ 2 := by
        field_simp; ring
      rw [this]; apply div_nonneg (by linarith) hb2.le
    have : Λ * Y / β ^ 2 = Λ * (Y / β ^ 2) := by ring
    have e5 : 2 * (X + Y) + Khi * (cX * X + cY * Y) = (2 + Khi * cX) * X + (2 + Khi * cY) * Y := by
      ring
    have e6 : Λ * (X + Y / β ^ 2) = Λ * X + Λ * (Y / β ^ 2) := by ring
    linarith
  -- step f
  have sf : 2 * k ^ 2 * (κ2 ^ 2 * a ^ 2 - 3 * κ2 * a) / T2
      - 2 * k ^ 2 * a ^ 2 / T2 ^ 2 * (cX * X + cY * Y) ≤ 2 * k ^ 2 * S / T2 ^ 2 := by
    have : 2 * k ^ 2 * (κ2 ^ 2 * a ^ 2 - 3 * κ2 * a) / T2
        - 2 * k ^ 2 * a ^ 2 / T2 ^ 2 * (cX * X + cY * Y)
        = 2 * k ^ 2 * (T2 * (κ2 ^ 2 * a ^ 2 - 3 * κ2 * a) - a ^ 2 * (cX * X + cY * Y)) / T2 ^ 2 := by
      field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have sf2 : 2 * k ^ 2 * a ^ 2 / T2 ^ 2 * (cX * X + cY * Y) ≤ Khi * (cX * X + cY * Y) :=
    mul_le_mul_of_nonneg_right hK hσ
  -- step g
  have sg : 2 * κ ^ 2 * (κ2 ^ 2 * τ ^ 2 * P ^ 2 - 3 * κ2 * τ * P) / (τ₂ * (τ * P ^ 3 + 125))
      ≤ 2 * k ^ 2 * (κ2 ^ 2 * a ^ 2 - 3 * κ2 * a) / T2 := by
    have g1 : 0 ≤ κ2 ^ 2 * τ ^ 2 * P ^ 2 - 3 * κ2 * τ * P := by
      have : κ2 ^ 2 * τ ^ 2 * P ^ 2 - 3 * κ2 * τ * P = κ2 * τ * P * (κ2 * τ * P - 3) := by ring
      rw [this]; apply mul_nonneg (by positivity); linarith
    have g2 : κ2 ^ 2 * τ ^ 2 * P ^ 2 - 3 * κ2 * τ * P ≤ κ2 ^ 2 * a ^ 2 - 3 * κ2 * a := by
      have : κ2 ^ 2 * a ^ 2 - 3 * κ2 * a - (κ2 ^ 2 * τ ^ 2 * P ^ 2 - 3 * κ2 * τ * P)
          = κ2 * (a - τ * P) * (κ2 * (a + τ * P) - 3) := by ring
      have h0 : 0 ≤ κ2 * (a - τ * P) * (κ2 * (a + τ * P) - 3) := by
        apply mul_nonneg (mul_nonneg hκ2.le (by linarith))
        have := mul_le_mul_of_nonneg_left ha1 hκ2.le
        have e : κ2 * (a + τ * P) = κ2 * a + κ2 * τ * P := by ring
        rw [e]; linarith
      linarith
    have g3 : κ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hκ hk1 2
    have g4 : T2 ≤ τ₂ * (τ * P ^ 3 + 125) := by
      rw [hT2def]; exact mul_le_mul_of_nonneg_left hT2 hτ₂.le
    calc 2 * κ ^ 2 * (κ2 ^ 2 * τ ^ 2 * P ^ 2 - 3 * κ2 * τ * P) / (τ₂ * (τ * P ^ 3 + 125))
        ≤ 2 * κ ^ 2 * (κ2 ^ 2 * τ ^ 2 * P ^ 2 - 3 * κ2 * τ * P) / T2 :=
          div_le_div_of_nonneg_left (by positivity) hT2pos g4
      _ ≤ 2 * k ^ 2 * (κ2 ^ 2 * a ^ 2 - 3 * κ2 * a) / T2 := by
          apply div_le_div_of_nonneg_right _ hT2pos.le
          have := mul_le_mul g3 g2 g1 (sq_nonneg k)
          linarith
  have sk : κ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hκ hk1 2
  have sT : (2 - Λ * δ - τ₂) * (τ * P ^ 3) ≤ (2 - Λ * δ - τ₂) * T :=
    mul_le_mul_of_nonneg_left hT1 hco
  have eT2 : T2 = τ₂ * T := rfl
  linarith

end OB
end Erdos30


set_option linter.all false

namespace Erdos30
namespace OB

noncomputable def pτ : ℝ := 407 / 400
noncomputable def pτ₂ : ℝ := 28 / 125
noncomputable def pα : ℝ := 507 / 2000
noncomputable def pβ : ℝ := 1097 / 2000
noncomputable def pδ : ℝ := 3183 / 20000
noncomputable def pΛ : ℝ := 9333527 / 1000000
noncomputable def pκ2 : ℝ := 1 - pα * pβ
noncomputable def pcX : ℝ := pκ2 ^ 2 - (1 - pα) ^ 2
noncomputable def pcY : ℝ := pκ2 ^ 2 - (pα * (1 - pβ)) ^ 2
noncomputable def pKhi : ℝ := 2 / pτ₂ ^ 2 * (1 + 1 / 10 ^ 6)
noncomputable def pμ : ℝ := 2 * (1 + pα * pβ) * pτ
noncomputable def pc0 : ℝ := 4 * (1 + pα * pβ)
noncomputable def pb : ℝ := 199405 / 100000

lemma num_hco : 0 ≤ 2 - pΛ * pδ - pτ₂ := by norm_num [pΛ, pδ, pτ₂]
lemma num_hΛ1 : 2 + pKhi * pcX ≤ pΛ := by
  norm_num [pKhi, pcX, pκ2, pα, pβ, pτ₂, pΛ]
lemma num_hΛ2 : pβ ^ 2 * (2 + pKhi * pcY) ≤ pΛ := by
  norm_num [pKhi, pcY, pκ2, pα, pβ, pτ₂, pΛ]
lemma num_cX : 0 ≤ pcX := by norm_num [pcX, pκ2, pα, pβ]
lemma num_cY : 0 ≤ pcY := by norm_num [pcY, pκ2, pα, pβ]

lemma num_h3 (P : ℝ) (hP : 10 ^ 7 ≤ P) : 3 ≤ pκ2 * pτ * P := by
  norm_num [pκ2, pα, pβ, pτ]; nlinarith

lemma num_hKhi (P : ℝ) (hP : 10 ^ 7 ≤ P) :
    2 * P ^ 4 * (pτ * P + 2) ^ 2 ≤ pKhi * (pτ₂ ^ 2 * pτ ^ 2 * P ^ 6) := by
  have hP0 : 0 < P := by linarith
  have key : (pτ * P + 2) ^ 2 ≤ (1 + 1 / 10 ^ 6) * pτ ^ 2 * P ^ 2 := by
    norm_num [pτ]; nlinarith
  have e : pKhi * (pτ₂ ^ 2 * pτ ^ 2 * P ^ 6) = 2 * P ^ 4 * ((1 + 1 / 10 ^ 6) * pτ ^ 2 * P ^ 2) := by
    unfold pKhi; field_simp; norm_num [pτ₂]
  rw [e]
  have : 0 ≤ 2 * P ^ 4 := by positivity
  exact mul_le_mul_of_nonneg_left key this

lemma num_poly (P : ℝ) (hP : 10 ^ 7 ≤ P) :
    P ^ 4 - pb * P ^ 3 ≤ (2 - pΛ * pδ - pτ₂) * pτ * P ^ 3 + (P ^ 2 - pμ * P - pc0) ^ 2
      - P ^ 3 / (pτ * pτ₂) + 2 * (P ^ 2 - pμ * P - pc0) ^ 2
        * (pκ2 ^ 2 * pτ ^ 2 * P ^ 2 - 3 * pκ2 * pτ * P) / (pτ₂ * (pτ * P ^ 3 + 125)) := by
  have hE : 0 < pτ₂ * (pτ * P ^ 3 + 125) := by
    unfold pτ₂ pτ; have : 0 < P := by linarith
    positivity
  rw [← sub_nonneg]
  have key : 0 ≤ pτ₂ * (pτ * P ^ 3 + 125) * ((2 - pΛ * pδ - pτ₂) * pτ * P ^ 3
      + (P ^ 2 - pμ * P - pc0) ^ 2 - P ^ 3 / (pτ * pτ₂) - (P ^ 4 - pb * P ^ 3))
      + 2 * (P ^ 2 - pμ * P - pc0) ^ 2 * (pκ2 ^ 2 * pτ ^ 2 * P ^ 2 - 3 * pκ2 * pτ * P) := by
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ P = t + 10 ^ 7 := ⟨P - 10 ^ 7, by linarith, by ring⟩
    simp only [pτ₂, pτ, pΛ, pδ, pμ, pc0, pκ2, pα, pβ, pb]
    ring_nf
    positivity
  have e : (2 - pΛ * pδ - pτ₂) * pτ * P ^ 3 + (P ^ 2 - pμ * P - pc0) ^ 2
      - P ^ 3 / (pτ * pτ₂) + 2 * (P ^ 2 - pμ * P - pc0) ^ 2
        * (pκ2 ^ 2 * pτ ^ 2 * P ^ 2 - 3 * pκ2 * pτ * P) / (pτ₂ * (pτ * P ^ 3 + 125))
      - (P ^ 4 - pb * P ^ 3)
      = (pτ₂ * (pτ * P ^ 3 + 125) * ((2 - pΛ * pδ - pτ₂) * pτ * P ^ 3
      + (P ^ 2 - pμ * P - pc0) ^ 2 - P ^ 3 / (pτ * pτ₂) - (P ^ 4 - pb * P ^ 3))
      + 2 * (P ^ 2 - pμ * P - pc0) ^ 2 * (pκ2 ^ 2 * pτ ^ 2 * P ^ 2 - 3 * pκ2 * pτ * P))
        / (pτ₂ * (pτ * P ^ 3 + 125)) := by
    have h1 : pτ ≠ 0 := by norm_num [pτ]
    have h2 : pτ₂ ≠ 0 := by norm_num [pτ₂]
    have h3 : pτ * P ^ 3 + 125 ≠ 0 := by
      have := hE.ne'; intro h; apply this; rw [h, mul_zero]
    rw [eq_div_iff hE.ne']
    field_simp
    ring
  rw [e]
  exact div_nonneg key hE.le

end OB
end Erdos30


set_option linter.all false

open Finset

namespace Erdos30
namespace OB

/-- Number of elements `< j`. -/
def Lc (A : Finset ℕ) (j : ℕ) : ℕ := (A.filter (fun a => a < j)).card
/-- Number of elements `> D - j`. -/
def Rc (A : Finset ℕ) (D j : ℕ) : ℕ := (A.filter (fun a => D + 1 ≤ a + j)).card

lemma Lc_mono (A : Finset ℕ) {i j : ℕ} (h : i ≤ j) : Lc A i ≤ Lc A j := by
  unfold Lc; apply card_le_card; intro a ha; simp only [mem_filter] at ha ⊢
  exact ⟨ha.1, by omega⟩

lemma Rc_mono (A : Finset ℕ) (D : ℕ) {i j : ℕ} (h : i ≤ j) : Rc A D i ≤ Rc A D j := by
  unfold Rc; apply card_le_card; intro a ha; simp only [mem_filter] at ha ⊢
  exact ⟨ha.1, by omega⟩

lemma Lc_succ (A : Finset ℕ) (j : ℕ) : Lc A (j + 1) ≤ Lc A j + 1 := by
  unfold Lc
  calc (A.filter (fun a => a < j + 1)).card ≤ (insert j (A.filter (fun a => a < j))).card := by
        apply card_le_card; intro a ha; simp only [mem_filter, mem_insert] at ha ⊢
        by_cases h : a = j
        · left; exact h
        · right; exact ⟨ha.1, by omega⟩
    _ ≤ _ := card_insert_le _ _

lemma Rc_succ (A : Finset ℕ) (D j : ℕ) : Rc A D (j + 1) ≤ Rc A D j + 1 := by
  unfold Rc
  calc (A.filter (fun a => D + 1 ≤ a + (j + 1))).card
      ≤ (insert (D - j) (A.filter (fun a => D + 1 ≤ a + j))).card := by
        apply card_le_card; intro a ha; simp only [mem_filter, mem_insert] at ha ⊢
        by_cases h : D + 1 ≤ a + j
        · right; exact ⟨ha.1, h⟩
        · left; omega
    _ ≤ _ := card_insert_le _ _

lemma Lc_zero (A : Finset ℕ) : Lc A 0 = 0 := by
  unfold Lc; simp

lemma Rc_zero (A : Finset ℕ) (D : ℕ) (hA : ∀ a ∈ A, a ≤ D) : Rc A D 0 = 0 := by
  unfold Rc; rw [card_eq_zero, filter_eq_empty_iff]
  intro a ha; have := hA a ha; omega

lemma W_left (A : Finset ℕ) (T j : ℕ) (hj : j ≤ T) : W A T j = Lc A j := by
  unfold W Lc; congr 1; apply filter_congr; intro a _; omega

lemma W_right (A : Finset ℕ) (D T j : ℕ) (hA : ∀ a ∈ A, a ≤ D) (hj : j ≤ T) :
    W A T (D + T + 1 - j) = Rc A D j := by
  unfold W Rc; congr 1; apply filter_congr; intro a ha; have := hA a ha; omega

lemma card_prs (X : Finset ℕ) : ((prs X).card : ℝ) = ((X.card : ℝ) ^ 2 - X.card) / 2 := by
  have h := sum_prod_symm X (fun _ _ => 1) (fun _ _ => rfl)
  simp only [sum_const, smul_eq_mul, mul_one, card_product] at h
  have : ((X.card * X.card : ℕ) : ℝ) = ((X.card + 2 * (prs X).card : ℕ) : ℝ) := by rw [h]
  push_cast at this
  linarith

lemma prs_pair_lb (X Y : Finset ℕ) :
    Qf ((X.card : ℝ) + Y.card) ≤ ((prs X).card : ℝ) + (prs Y).card := by
  rw [card_prs, card_prs]; unfold Qf
  nlinarith [sq_nonneg ((X.card : ℝ) - Y.card)]

lemma pair_sum_lb (X X1 X2 : Finset ℕ) (T2 m1 m2 : ℕ) (h1 : X1 ⊆ X) (h2 : X2 ⊆ X)
    (hd : Disjoint X1 X2)
    (hX : ∀ p ∈ prs X, p.2 - p.1 ≤ m2) (hX1 : ∀ p ∈ prs X1, p.2 - p.1 ≤ m1)
    (hX2 : ∀ p ∈ prs X2, p.2 - p.1 ≤ m2 - m1) (hm : m1 ≤ m2) (hm2 : m2 ≤ T2) :
    ((prs X).card : ℝ) * ((T2 : ℝ) - m2) + ((prs X1).card : ℝ) * ((m2 : ℝ) - m1)
      + ((prs X2).card : ℝ) * m1 ≤ ∑ p ∈ prs X, ((T2 - (p.2 - p.1) : ℕ) : ℝ) := by
  have s1 : prs X1 ⊆ prs X := prs_mono h1
  have s2 : prs X2 ⊆ prs X := prs_mono h2
  have dd : Disjoint (prs X1) (prs X2) := prs_disj hd
  -- pointwise lower bound
  have hpt : ∀ p ∈ prs X, ((T2 : ℝ) - m2) + (if p ∈ prs X1 then ((m2 : ℝ) - m1) else 0)
      + (if p ∈ prs X2 then (m1 : ℝ) else 0) ≤ ((T2 - (p.2 - p.1) : ℕ) : ℝ) := by
    intro p hp
    have hle := hX p hp
    rw [Nat.cast_sub (show p.2 - p.1 ≤ T2 by omega)]
    by_cases ha : p ∈ prs X1
    · have hb : p ∉ prs X2 := disjoint_left.1 dd ha
      have := hX1 p ha
      simp only [ha, hb, if_true, if_false]
      have : ((p.2 - p.1 : ℕ) : ℝ) ≤ m1 := by exact_mod_cast this
      linarith
    · by_cases hb : p ∈ prs X2
      · have := hX2 p hb
        simp only [ha, hb, if_true, if_false]
        have : ((p.2 - p.1 : ℕ) : ℝ) ≤ ((m2 - m1 : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub hm] at this
        linarith
      · simp only [ha, hb, if_false]
        have : ((p.2 - p.1 : ℕ) : ℝ) ≤ m2 := by exact_mod_cast hle
        linarith
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, sum_const, sum_ite_mem, sum_ite_mem,
    inter_eq_right.2 s1, inter_eq_right.2 s2, sum_const, sum_const] at hsum
  simp only [nsmul_eq_mul] at hsum
  linarith

end OB
end Erdos30


set_option linter.all false

open Finset

namespace Erdos30
namespace OB

lemma realA (P T D c τ : ℝ) (hτ : 0 < τ) (hP : 1 ≤ P) (hT1 : τ * P ^ 3 ≤ T)
    (hT2 : T ≤ τ * P ^ 3 + 125) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (h : (P ^ 2 * T) ^ 2 ≤ (D + T) * T * (T + c * P ^ 2)) :
    P ^ 4 - (τ + c / τ) * P ^ 3 - 125 ≤ D := by
  by_contra hlt; push_neg at hlt
  have hP0 : 0 < P := by linarith
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT1
  have e0 : (τ + c / τ) * P ^ 3 = τ * P ^ 3 + c / τ * P ^ 3 := by ring
  have h1 : D + T < P ^ 4 - c / τ * P ^ 3 := by linarith
  have hpos : 0 < T + c * P ^ 2 := by positivity
  have h2 : (D + T) * (T + c * P ^ 2) < (P ^ 4 - c / τ * P ^ 3) * (T + c * P ^ 2) :=
    mul_lt_mul_of_pos_right h1 hpos
  have h3 : (P ^ 4 - c / τ * P ^ 3) * (T + c * P ^ 2) ≤ P ^ 4 * T := by
    have e : (P ^ 4 - c / τ * P ^ 3) * (T + c * P ^ 2)
        = P ^ 4 * T + c * P ^ 3 * (P ^ 3 - T / τ) - c ^ 2 / τ * P ^ 5 := by
      field_simp; ring
    have h4 : P ^ 3 - T / τ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hτ]; linarith
    have h5 : 0 ≤ c ^ 2 / τ * P ^ 5 := by positivity
    have h6 : c * P ^ 3 * (P ^ 3 - T / τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h4
    linarith
  have : (D + T) * T * (T + c * P ^ 2) < (P ^ 2 * T) ^ 2 := by
    calc (D + T) * T * (T + c * P ^ 2) = ((D + T) * (T + c * P ^ 2)) * T := by ring
      _ < ((P ^ 4 - c / τ * P ^ 3) * (T + c * P ^ 2)) * T := mul_lt_mul_of_pos_right h2 hT0
      _ ≤ (P ^ 4 * T) * T := mul_le_mul_of_nonneg_right h3 hT0.le
      _ = (P ^ 2 * T) ^ 2 := by ring
  linarith

lemma num_triv (P : ℝ) (hP : 10 ^ 7 ≤ P) : P ^ 4 - pb * P ^ 3 ≤ P ^ 4 - (pτ * P ^ 3 + 125) := by
  have h3 : (10 ^ 21 : ℝ) ≤ P ^ 3 := by
    calc (10 ^ 21 : ℝ) = (10 ^ 7) ^ 3 := by norm_num
      _ ≤ P ^ 3 := pow_le_pow_left₀ (by norm_num) hP 3
  norm_num [pb, pτ]; nlinarith

lemma num_ET (P : ℝ) (hP : 10 ^ 7 ≤ P) :
    2 * (pτ * P ^ 3 + 125) + 2 ≤ P ^ 4 - (pτ + 1 / pτ) * P ^ 3 - 125 := by
  have h3 : (10 ^ 21 : ℝ) ≤ P ^ 3 := by
    calc (10 ^ 21 : ℝ) = (10 ^ 7) ^ 3 := by norm_num
      _ ≤ P ^ 3 := pow_le_pow_left₀ (by norm_num) hP 3
  have h4 : P ^ 4 = P * P ^ 3 := by ring
  have h5 : 10 ^ 7 * P ^ 3 ≤ P * P ^ 3 := mul_le_mul_of_nonneg_right hP (by positivity)
  norm_num [pτ]; nlinarith

lemma num_A (P : ℝ) (hP : 10 ^ 7 ≤ P) :
    P ^ 4 - pb * P ^ 3 ≤ P ^ 4 - (pτ + (1 - 2 * pα ^ 2 * pβ ^ 2 * pδ * pτ ^ 2) / pτ) * P ^ 3 - 125 := by
  have h3 : (10 ^ 21 : ℝ) ≤ P ^ 3 := by
    calc (10 ^ 21 : ℝ) = (10 ^ 7) ^ 3 := by norm_num
      _ ≤ P ^ 3 := pow_le_pow_left₀ (by norm_num) hP 3
  norm_num [pb, pτ, pα, pβ, pδ]; nlinarith

lemma mem_prs (X : Finset ℕ) (p : ℕ × ℕ) : p ∈ prs X ↔ p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 < p.2 := by
  simp only [prs, mem_filter, mem_product, and_assoc]

lemma card_three (A : Finset ℕ) (D z : ℕ) (hz : 2 * z ≤ D) :
    (A.filter (fun x => x < z)).card + (A.filter (fun x => D + 1 ≤ x + z)).card
      + (A.filter (fun x => z ≤ x ∧ x + z ≤ D)).card = A.card := by
  have h1 := card_filter_add_card_filter_not (s := A) (fun x => x < z)
  have h2 := card_filter_add_card_filter_not (s := A.filter (fun x => ¬ x < z))
    (fun x => D + 1 ≤ x + z)
  rw [filter_filter, filter_filter] at h2
  have e1 : A.filter (fun x => ¬ x < z ∧ D + 1 ≤ x + z) = A.filter (fun x => D + 1 ≤ x + z) := by
    apply filter_congr; intro x _; omega
  have e2 : A.filter (fun x => ¬ x < z ∧ ¬ D + 1 ≤ x + z) = A.filter (fun x => z ≤ x ∧ x + z ≤ D) := by
    apply filter_congr; intro x _; omega
  rw [e1, e2] at h2
  omega

lemma num_kappa (P : ℝ) (hP : 10 ^ 7 ≤ P) : 0 ≤ P ^ 2 - pμ * P - pc0 := by
  have h : 10 ^ 7 * P ≤ P * P := mul_le_mul_of_nonneg_right hP (by linarith)
  norm_num [pμ, pc0, pα, pβ, pτ]; nlinarith

lemma num_abig (P a : ℝ) (hP : 10 ^ 7 ≤ P) (ha : pτ * P ≤ a) :
    1 ≤ 2 * (1 - pα) * a - 2 ∧ 1 ≤ 2 * (1 - pα * pβ) * a - 2 - 2 * (1 - pα) * a := by
  norm_num [pτ] at ha; norm_num [pα, pβ]; constructor <;> linarith

set_option maxHeartbeats 4000000 in
/-- Main diameter bound: a Sidon set of `k ≥ 10^14` elements inside `[0, D]` has
`D ≥ k² - 1.99405 k^{3/2}`. -/
theorem diam_bound (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (D : ℕ) (hAD : ∀ a ∈ A, a ≤ D)
    (hk : (10 ^ 7 : ℝ) ≤ Real.sqrt A.card) :
    Real.sqrt A.card ^ 4 - pb * Real.sqrt A.card ^ 3 ≤ D := by
  classical
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = A.card := ⟨_, rfl⟩
  rw [← hkdef] at hk ⊢
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Real.sqrt k := ⟨_, rfl⟩
  rw [← hPdef] at hk ⊢
  have hP0 : 0 < P := by linarith
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have hkP : (k : ℝ) = P ^ 2 := by rw [hPdef, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hτpos : (0 : ℝ) < pτ := by norm_num [pτ]
  -- window lengths
  obtain ⟨v, hv1, hv2⟩ : ∃ v : ℕ, pτ * P ^ 3 / 125 ≤ v ∧ (v : ℝ) < pτ * P ^ 3 / 125 + 1 :=
    ⟨_, Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = 125 * v := ⟨_, rfl⟩
  obtain ⟨T2, hT2def⟩ : ∃ T2 : ℕ, T2 = 28 * v := ⟨_, rfl⟩
  have hT1 : pτ * P ^ 3 ≤ (T : ℝ) := by rw [hTdef]; push_cast; linarith
  have hT2 : (T : ℝ) ≤ pτ * P ^ 3 + 125 := by rw [hTdef]; push_cast; linarith
  have hT2r : (T2 : ℝ) = pτ₂ * T := by rw [hT2def, hTdef, pτ₂]; push_cast; ring
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT1
  have hT1n : 1 ≤ T := by
    have : 0 < T := by exact_mod_cast hTpos
    omega
  have hAr : ∀ a ∈ A, 0 ≤ a ∧ a ≤ 0 + D := fun a ha => ⟨Nat.zero_le _, by simpa using hAD a ha⟩
  -- Erdős–Turán
  have hET : ((k : ℝ) * T) ^ 2 ≤ ((D : ℝ) + T) * ((k : ℝ) * T + (T : ℝ) * ((T : ℝ) - 1)) := by
    have := hkdef ▸ core A A ∅ ∅ hA subset_rfl (empty_subset _) (empty_subset _)
      (disjoint_empty_right _) (disjoint_empty_right _) (disjoint_empty_left _) 0 D T hT1n hAr
      ∅ (empty_subset _)
    simp only [sum_empty, mul_zero, add_zero, prs, empty_product, filter_empty] at this
    exact this
  have hM0 : (0 : ℝ) < (D : ℝ) + T := by positivity
  have hDlow : P ^ 4 - (pτ + 1 / pτ) * P ^ 3 - 125 ≤ (D : ℝ) := by
    apply realA P T D 1 pτ hτpos hP1 hT1 hT2 zero_le_one (Nat.cast_nonneg _)
    have e : ((D : ℝ) + T) * T * (T + 1 * P ^ 2)
        = ((D : ℝ) + T) * ((k : ℝ) * T + (T : ℝ) * ((T : ℝ) - 1)) + ((D : ℝ) + T) * T := by
      rw [hkP]; ring
    have e' : (P ^ 2 * (T : ℝ)) ^ 2 = ((k : ℝ) * T) ^ 2 := by rw [hkP]
    rw [e', e]; linarith [mul_pos hM0 hTpos]
  have hD2T : 2 * T + 2 ≤ D := by
    have := num_ET P hk
    have : (2 * T + 2 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  set a : ℝ := (k : ℝ) * T / ((D : ℝ) + T) with hadef
  have haM : a * ((D : ℝ) + T) = k * T := by rw [hadef]; field_simp
  have hk0 : (0 : ℝ) < k := by rw [hkP]; positivity
  have ha2 : a ≤ pτ * P + 2 := by
    have h1 : ((D : ℝ) + T) * (k * T * a) ≤ ((D : ℝ) + T) * ((k : ℝ) * T + (T : ℝ) * ((T : ℝ) - 1)) := by
      calc ((D : ℝ) + T) * (k * T * a) = ((k : ℝ) * T) * (a * ((D : ℝ) + T)) := by ring
        _ = ((k : ℝ) * T) ^ 2 := by rw [haM]; ring
        _ ≤ _ := hET
    have h2 := le_of_mul_le_mul_left h1 hM0
    have h3 : k * a ≤ k + T := by
      have : T * (k * a) ≤ T * (k + T) := by
        have e1 : (T : ℝ) * (k * a) = k * T * a := by ring
        have e2 : (T : ℝ) * (k + T) = k * T + T * (T - 1) + T := by ring
        rw [e1, e2]; linarith
      exact le_of_mul_le_mul_left this hTpos
    have h4 : P ^ 2 * a ≤ P ^ 2 * (pτ * P + 2) := by
      rw [← hkP]
      have h5 : (125 : ℝ) ≤ P ^ 2 := by
        have := mul_le_mul hk hk (by norm_num) hP0.le
        rw [sq]; linarith
      have e : (k : ℝ) * (pτ * P + 2) = pτ * P ^ 3 + 2 * k := by rw [hkP]; ring
      rw [e]; rw [← hkP] at h5; linarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  by_cases htriv : ((k : ℝ)) ^ 2 < (D : ℝ) + T
  · -- trivial case
    have := num_triv P hk
    rw [hkP] at htriv
    have e : (P ^ 2) ^ 2 = P ^ 4 := by ring
    rw [e] at htriv
    linarith
  push_neg at htriv
  have ha1 : pτ * P ≤ a := by
    have h1 : (k : ℝ) * T ≤ a * k ^ 2 := by
      rw [← haM]; exact mul_le_mul_of_nonneg_left htriv (by
        rw [hadef]; positivity)
    have h2 : (T : ℝ) ≤ a * k := by
      have : (k : ℝ) * T ≤ k * (a * k) := by
        have e : (k : ℝ) * (a * k) = a * k ^ 2 := by ring
        rw [e]; exact h1
      exact le_of_mul_le_mul_left this hk0
    rw [hkP] at h2
    have : P ^ 2 * (pτ * P) ≤ P ^ 2 * a := by
      have e1 : P ^ 2 * (pτ * P) = pτ * P ^ 3 := by ring
      have e2 : P ^ 2 * a = a * P ^ 2 := by ring
      rw [e1, e2]; linarith
    exact le_of_mul_le_mul_left this (by positivity)
  have ha0 : 0 ≤ a := le_trans (by positivity) ha1
  -- the profile G
  set G : ℕ → ℕ := fun j => Lc A j + Rc A D j with hGdef
  have hGmono : ∀ i j, i ≤ j → G i ≤ G j := fun i j h =>
    Nat.add_le_add (Lc_mono A h) (Rc_mono A D h)
  have hGsucc : ∀ j, G (j + 1) ≤ G j + 2 := fun j => by
    have := Lc_succ A j; have := Rc_succ A D j; simp only [hGdef]; omega
  have hG0 : G 0 = 0 := by simp only [hGdef, Lc_zero, Rc_zero A D hAD]
  set F := (Icc 1 T).filter (fun j => 2 * pα * a ≤ |(G j : ℝ) - 2 * a|) with hFdef
  set Mid := (Icc 1 T).filter (fun j => 2 * pα * pβ * a ≤ |(G j : ℝ) - 2 * a|
    ∧ |(G j : ℝ) - 2 * a| < 2 * pα * a) with hMiddef
  have hFM : Disjoint F Mid := by
    rw [disjoint_left]; intro j hj hj'
    simp only [hFdef, hMiddef, mem_filter] at hj hj'
    linarith [hj.2, hj'.2.2]
  by_cases hcase : pβ ^ 2 * pδ * T ≤ (F.card : ℝ) + pβ ^ 2 * Mid.card
  · -- Case A: large variance
    have hJ' : Icc 1 T ∪ (Icc 1 T).image (fun j => D + T + 1 - j) ⊆ Icc (0 + 1) (0 + D + T) := by
      intro j hj; simp only [mem_union, mem_image, mem_Icc] at hj ⊢
      rcases hj with h | ⟨i, hi, rfl⟩ <;> omega
    have hc := hkdef ▸ core A A ∅ ∅ hA subset_rfl (empty_subset _) (empty_subset _)
      (disjoint_empty_right _) (disjoint_empty_right _) (disjoint_empty_left _) 0 D T hT1n hAr
      _ hJ'
    simp only [prs, empty_product, filter_empty, sum_empty, add_zero, mul_zero] at hc
    rw [← hadef] at hc
    have hdisj : Disjoint (Icc 1 T) ((Icc 1 T).image (fun j => D + T + 1 - j)) := by
      rw [disjoint_left]; intro j hj hj'
      simp only [mem_image, mem_Icc] at hj hj'
      obtain ⟨i, hi, rfl⟩ := hj'; omega
    have hinj : Set.InjOn (fun j => D + T + 1 - j) (Icc 1 T : Set ℕ) := by
      intro i hi j hj h; simp only [coe_Icc, Set.mem_Icc] at hi hj; simp only at h; omega
    rw [sum_union hdisj, sum_image hinj] at hc
    have hV : ∑ j ∈ Icc 1 T, (((G j : ℝ) - 2 * a) ^ 2 / 2)
        ≤ ∑ j ∈ Icc 1 T, ((W A T j : ℝ) - a) ^ 2
          + ∑ j ∈ Icc 1 T, ((W A T (D + T + 1 - j) : ℝ) - a) ^ 2 := by
      rw [← sum_add_distrib]
      apply sum_le_sum; intro j hj
      simp only [mem_Icc] at hj
      rw [W_left A T j hj.2, W_right A D T j hAD hj.2]
      simp only [hGdef]; push_cast
      have e : ((Lc A j : ℝ) - a) ^ 2 + ((Rc A D j : ℝ) - a) ^ 2
          = ((Lc A j : ℝ) + Rc A D j - 2 * a) ^ 2 / 2 + ((Lc A j : ℝ) - Rc A D j) ^ 2 / 2 := by ring
      rw [e]; linarith [sq_nonneg ((Lc A j : ℝ) - Rc A D j)]
    have hFM' : F ∪ Mid ⊆ Icc 1 T := union_subset (filter_subset _ _) (filter_subset _ _)
    have hV2 : ∑ j ∈ F ∪ Mid, (((G j : ℝ) - 2 * a) ^ 2 / 2)
        ≤ ∑ j ∈ Icc 1 T, (((G j : ℝ) - 2 * a) ^ 2 / 2) :=
      sum_le_sum_of_subset_of_nonneg hFM' (fun _ _ _ => by positivity)
    rw [sum_union hFM] at hV2
    have hF : (F.card : ℝ) * (2 * pα ^ 2 * a ^ 2) ≤ ∑ j ∈ F, (((G j : ℝ) - 2 * a) ^ 2 / 2) := by
      have := card_nsmul_le_sum F (fun j => ((G j : ℝ) - 2 * a) ^ 2 / 2) (2 * pα ^ 2 * a ^ 2) (by
        intro j hj
        simp only [hFdef, mem_filter] at hj
        have h0 : 0 ≤ 2 * pα * a := by
          have : (0:ℝ) < pα := by norm_num [pα]
          positivity
        have := pow_le_pow_left₀ h0 hj.2 2
        rw [sq_abs] at this
        show 2 * pα ^ 2 * a ^ 2 ≤ ((G j : ℝ) - 2 * a) ^ 2 / 2
        linarith [show (2 * pα * a) ^ 2 = 4 * (pα ^ 2 * a ^ 2) by ring])
      rwa [nsmul_eq_mul] at this
    have hMd : (Mid.card : ℝ) * (2 * pα ^ 2 * pβ ^ 2 * a ^ 2)
        ≤ ∑ j ∈ Mid, (((G j : ℝ) - 2 * a) ^ 2 / 2) := by
      have := card_nsmul_le_sum Mid (fun j => ((G j : ℝ) - 2 * a) ^ 2 / 2)
        (2 * pα ^ 2 * pβ ^ 2 * a ^ 2) (by
        intro j hj
        simp only [hMiddef, mem_filter] at hj
        have h0 : 0 ≤ 2 * pα * pβ * a := by
          have : (0:ℝ) < pα := by norm_num [pα]
          have : (0:ℝ) < pβ := by norm_num [pβ]
          positivity
        have := pow_le_pow_left₀ h0 hj.2.1 2
        rw [sq_abs] at this
        show 2 * pα ^ 2 * pβ ^ 2 * a ^ 2 ≤ ((G j : ℝ) - 2 * a) ^ 2 / 2
        linarith [show (2 * pα * pβ * a) ^ 2 = 4 * (pα ^ 2 * pβ ^ 2 * a ^ 2) by ring])
      rwa [nsmul_eq_mul] at this
    have ha2' : pτ ^ 2 * P ^ 2 ≤ a ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) ha1 2
      rwa [mul_pow] at this
    have hVlow : 2 * pα ^ 2 * pβ ^ 2 * pδ * pτ ^ 2 * P ^ 2 * T
        ≤ ∑ j ∈ Icc 1 T, ((W A T j : ℝ) - a) ^ 2
          + ∑ j ∈ Icc 1 T, ((W A T (D + T + 1 - j) : ℝ) - a) ^ 2 := by
      have e1 : 2 * pα ^ 2 * a ^ 2 * (pβ ^ 2 * pδ * T)
          ≤ 2 * pα ^ 2 * a ^ 2 * ((F.card : ℝ) + pβ ^ 2 * Mid.card) :=
        mul_le_mul_of_nonneg_left hcase (by positivity)
      have e2 : 2 * pα ^ 2 * pβ ^ 2 * pδ * pτ ^ 2 * P ^ 2 * T
          ≤ 2 * pα ^ 2 * a ^ 2 * (pβ ^ 2 * pδ * T) := by
        have h0 : 0 ≤ 2 * pα ^ 2 * pβ ^ 2 * pδ * (T : ℝ) := by
          have : (0:ℝ) < pδ := by norm_num [pδ]
          positivity
        calc 2 * pα ^ 2 * pβ ^ 2 * pδ * pτ ^ 2 * P ^ 2 * T
            = (2 * pα ^ 2 * pβ ^ 2 * pδ * (T : ℝ)) * (pτ ^ 2 * P ^ 2) := by ring
          _ ≤ (2 * pα ^ 2 * pβ ^ 2 * pδ * (T : ℝ)) * a ^ 2 := mul_le_mul_of_nonneg_left ha2' h0
          _ = 2 * pα ^ 2 * a ^ 2 * (pβ ^ 2 * pδ * T) := by ring
      have e3 : 2 * pα ^ 2 * a ^ 2 * ((F.card : ℝ) + pβ ^ 2 * Mid.card)
          = (F.card : ℝ) * (2 * pα ^ 2 * a ^ 2) + (Mid.card : ℝ) * (2 * pα ^ 2 * pβ ^ 2 * a ^ 2) := by
        ring
      linarith
    have hfin : (P ^ 2 * (T : ℝ)) ^ 2 ≤ ((D : ℝ) + T) * T
        * (T + (1 - 2 * pα ^ 2 * pβ ^ 2 * pδ * pτ ^ 2) * P ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hVlow hM0.le
      have e1 : (P ^ 2 * (T : ℝ)) ^ 2 = ((k : ℝ) * T) ^ 2 := by rw [hkP]
      have e : ((D : ℝ) + T) * T * (T + (1 - 2 * pα ^ 2 * pβ ^ 2 * pδ * pτ ^ 2) * P ^ 2)
          = ((D : ℝ) + T) * ((k : ℝ) * T + (T : ℝ) * ((T : ℝ) - 1))
            + ((D : ℝ) + T) * T
            - ((D : ℝ) + T) * (2 * pα ^ 2 * pβ ^ 2 * pδ * pτ ^ 2 * P ^ 2 * T) := by
        rw [hkP]; ring
      rw [e1, e]
      linarith [mul_pos hM0 hTpos]
    have hc' : 0 ≤ 1 - 2 * pα ^ 2 * pβ ^ 2 * pδ * pτ ^ 2 := by norm_num [pα, pβ, pδ, pτ]
    have := realA P T D _ pτ hτpos hP1 hT1 hT2 hc' (Nat.cast_nonneg _) hfin
    have := num_A P hk
    linarith
  · -- Case B: small variance; the ends are dense
    push_neg at hcase
    have hα0 : (0:ℝ) < pα := by norm_num [pα]
    have hα1 : pα < 1 := by norm_num [pα]
    have hβ0 : (0:ℝ) < pβ := by norm_num [pβ]
    have hβ1 : pβ < 1 := by norm_num [pβ]
    have hδτ₂ : pδ < pτ₂ := by norm_num [pδ, pτ₂]
    have hδ1 : pδ < 1 := by norm_num [pδ]
    have hδ0 : (0:ℝ) < pδ := by norm_num [pδ]
    have hτ₂0 : (0:ℝ) < pτ₂ := by norm_num [pτ₂]
    have ha0' : 0 < a := lt_of_lt_of_le (by positivity) ha1
    obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = 2 * (1 - pα) * a := ⟨_, rfl⟩
    obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = 2 * (1 - pα * pβ) * a := ⟨_, rfl⟩
    obtain ⟨c3, hc3⟩ : ∃ c : ℝ, c = 2 * (1 + pα * pβ) * a := ⟨_, rfl⟩
    have hc1n : 0 ≤ c1 := by rw [hc1]; apply mul_nonneg _ ha0; linarith
    have hαβ : pα * pβ < pα := mul_lt_of_lt_one_right hα0 hβ1
    have hαβ0 : 0 < pα * pβ := by positivity
    have hc12 : c1 ≤ c2 := by rw [hc1, hc2]; exact mul_le_mul_of_nonneg_right (by linarith) ha0
    have hc23 : c2 < c3 := by rw [hc2, hc3]; exact mul_lt_mul_of_pos_right (by linarith) ha0'
    have hG0r : ((G 0 : ℕ) : ℝ) = 0 := by rw [hG0]; simp
    obtain ⟨m1, hm1⟩ : ∃ m, m = Nat.findGreatest (fun j => ((G j : ℕ) : ℝ) ≤ c1) T := ⟨_, rfl⟩
    obtain ⟨m2, hm2⟩ : ∃ m, m = Nat.findGreatest (fun j => ((G j : ℕ) : ℝ) ≤ c2) T := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ m, m = Nat.findGreatest (fun j => ((G j : ℕ) : ℝ) < c3) T := ⟨_, rfl⟩
    have hm1T : m1 ≤ T := hm1 ▸ Nat.findGreatest_le T
    have hm2T : m2 ≤ T := hm2 ▸ Nat.findGreatest_le T
    have hzT : z ≤ T := hz ▸ Nat.findGreatest_le T
    have hPm1 : ((G m1 : ℕ) : ℝ) ≤ c1 := hm1 ▸ Nat.findGreatest_spec (P := fun j => ((G j : ℕ) : ℝ) ≤ c1)
      (Nat.zero_le T) (by rw [hG0r]; exact hc1n)
    have hPm2 : ((G m2 : ℕ) : ℝ) ≤ c2 := hm2 ▸ Nat.findGreatest_spec (P := fun j => ((G j : ℕ) : ℝ) ≤ c2)
      (Nat.zero_le T) (by rw [hG0r]; linarith)
    have hPz : ((G z : ℕ) : ℝ) < c3 := hz ▸ Nat.findGreatest_spec (P := fun j => ((G j : ℕ) : ℝ) < c3)
      (Nat.zero_le T) (by rw [hG0r]; linarith)
    have hm12 : m1 ≤ m2 := hm2 ▸ Nat.le_findGreatest hm1T (le_trans hPm1 hc12)
    have hm2z : m2 ≤ z := hz ▸ Nat.le_findGreatest hm2T (lt_of_le_of_lt hPm2 hc23)
    have hgt1 : ∀ j, m1 < j → j ≤ T → c1 < ((G j : ℕ) : ℝ) := fun j h1 h2 =>
      lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun j => ((G j : ℕ) : ℝ) ≤ c1) (hm1 ▸ h1) h2)
    have hgt2 : ∀ j, m2 < j → j ≤ T → c2 < ((G j : ℕ) : ℝ) := fun j h1 h2 =>
      lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun j => ((G j : ℕ) : ℝ) ≤ c2) (hm2 ▸ h1) h2)
    have hgt3 : ∀ j, z < j → j ≤ T → c3 ≤ ((G j : ℕ) : ℝ) := fun j h1 h2 =>
      le_of_not_gt (Nat.findGreatest_is_greatest (P := fun j => ((G j : ℕ) : ℝ) < c3) (hz ▸ h1) h2)
    have hGmr : ∀ i j, i ≤ j → ((G i : ℕ) : ℝ) ≤ ((G j : ℕ) : ℝ) := fun i j h => by
      exact_mod_cast hGmono i j h
    -- the level sets
    have s1 : Icc 1 m1 ⊆ F := by
      intro j hj; simp only [mem_Icc] at hj
      simp only [hFdef, mem_filter, mem_Icc]
      refine ⟨⟨hj.1, by omega⟩, ?_⟩
      have := le_trans (hGmr j m1 hj.2) hPm1
      rw [hc1] at this
      exact le_abs.2 (Or.inr (by linarith))
    have s2 : Ioc m1 m2 ⊆ Mid := by
      intro j hj; simp only [mem_Ioc] at hj
      simp only [hMiddef, mem_filter, mem_Icc]
      have h1 := hgt1 j hj.1 (by omega)
      have h2 := le_trans (hGmr j m2 hj.2) hPm2
      rw [hc1] at h1; rw [hc2] at h2
      have hneg : ((G j : ℕ) : ℝ) - 2 * a < 0 := by
        have := mul_pos hαβ0 ha0'; linarith
      rw [abs_of_neg hneg]
      exact ⟨⟨by omega, by omega⟩, by linarith, by linarith⟩
    have s3 : Ioc z T ⊆ F ∪ Mid := by
      intro j hj; simp only [mem_Ioc] at hj
      have h3 := hgt3 j hj.1 hj.2
      rw [hc3] at h3
      have hpos : 0 ≤ ((G j : ℕ) : ℝ) - 2 * a := by
        have := mul_pos hαβ0 ha0'; linarith
      rw [mem_union]
      by_cases hh : 2 * pα * a ≤ |((G j : ℕ) : ℝ) - 2 * a|
      · left; simp only [hFdef, mem_filter, mem_Icc]; exact ⟨⟨by omega, hj.2⟩, hh⟩
      · right; simp only [hMiddef, mem_filter, mem_Icc]
        push_neg at hh
        refine ⟨⟨by omega, hj.2⟩, ?_, hh⟩
        rw [abs_of_nonneg hpos]; linarith
    have hcm1 : m1 ≤ F.card := by
      have := card_le_card s1; simpa using this
    have hcm2 : m2 - m1 ≤ Mid.card := by
      have := card_le_card s2; simpa using this
    have hcz : m2 + (T - z) ≤ F.card + Mid.card := by
      have hsub : Icc 1 m2 ∪ Ioc z T ⊆ F ∪ Mid := by
        apply union_subset _ s3
        intro j hj; simp only [mem_Icc] at hj
        by_cases hj1 : j ≤ m1
        · exact mem_union_left _ (s1 (by simp only [mem_Icc]; omega))
        · exact mem_union_right _ (s2 (by simp only [mem_Ioc]; omega))
      have hd : Disjoint (Icc 1 m2) (Ioc z T) := by
        rw [disjoint_left]; intro j h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
      have := card_le_card hsub
      rw [card_union_of_disjoint hd, card_union_of_disjoint hFM] at this
      simpa using this
    -- real bookkeeping
    have hβ2 : 0 < pβ ^ 2 := by positivity
    have hβ21 : pβ ^ 2 < 1 := by norm_num [pβ]
    have hFr : (0:ℝ) ≤ F.card := Nat.cast_nonneg _
    have hMr : (0:ℝ) ≤ Mid.card := Nat.cast_nonneg _
    have hXY : (F.card : ℝ) + Mid.card < pδ * T := by
      have h1 : pβ ^ 2 * (F.card : ℝ) ≤ F.card := mul_le_of_le_one_left hFr hβ21.le
      have h2 : pβ ^ 2 * ((F.card : ℝ) + Mid.card) < pβ ^ 2 * (pδ * T) := by linarith
      exact lt_of_mul_lt_mul_left h2 hβ2.le
    have hm2r : (m2 : ℝ) < pδ * T := by
      have : (m2 : ℝ) ≤ F.card + Mid.card := by
        have : m2 ≤ F.card + Mid.card := by omega
        exact_mod_cast this
      linarith
    have hm2T' : m2 < T := by
      have : (m2 : ℝ) < T := by
        have := mul_lt_mul_of_pos_right hδ1 hTpos; linarith
      exact_mod_cast this
    have hm2T2 : m2 ≤ T2 := by
      have : (m2 : ℝ) ≤ T2 := by
        rw [hT2r]; have := mul_le_mul_of_nonneg_right hδτ₂.le hTpos.le; linarith
      exact_mod_cast this
    have hl : c2 - 2 ≤ ((G m2 : ℕ) : ℝ) := by
      have h1 := hgt2 (m2 + 1) (by omega) (by omega)
      have h2 : ((G (m2 + 1) : ℕ) : ℝ) ≤ ((G m2 : ℕ) : ℝ) + 2 := by exact_mod_cast hGsucc m2
      linarith
    have hl1 : c1 - 2 ≤ ((G m1 : ℕ) : ℝ) := by
      have h1 := hgt1 (m1 + 1) (by omega) (by omega)
      have h2 : ((G (m1 + 1) : ℕ) : ℝ) ≤ ((G m1 : ℕ) : ℝ) + 2 := by exact_mod_cast hGsucc m1
      linarith
    have hl2 : c2 - 2 - c1 ≤ ((G m2 : ℕ) : ℝ) - ((G m1 : ℕ) : ℝ) := by linarith
    -- the end sets and the middle set
    obtain ⟨L, hL⟩ : ∃ X : Finset ℕ, X = A.filter (fun x => x < m2) := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ X : Finset ℕ, X = A.filter (fun x => D + 1 ≤ x + m2) := ⟨_, rfl⟩
    obtain ⟨L1, hL1⟩ : ∃ X : Finset ℕ, X = L.filter (fun x => x < m1) := ⟨_, rfl⟩
    obtain ⟨L2, hL2⟩ : ∃ X : Finset ℕ, X = L.filter (fun x => ¬ x < m1) := ⟨_, rfl⟩
    obtain ⟨R1, hR1⟩ : ∃ X : Finset ℕ, X = R.filter (fun x => D + 1 ≤ x + m1) := ⟨_, rfl⟩
    obtain ⟨R2, hR2⟩ : ∃ X : Finset ℕ, X = R.filter (fun x => ¬ D + 1 ≤ x + m1) := ⟨_, rfl⟩
    obtain ⟨Mm, hMm⟩ : ∃ X : Finset ℕ, X = A.filter (fun x => z ≤ x ∧ x + z ≤ D) := ⟨_, rfl⟩
    have mL : ∀ x, x ∈ L ↔ x ∈ A ∧ x < m2 := fun x => by rw [hL, mem_filter]
    have mR : ∀ x, x ∈ R ↔ x ∈ A ∧ D + 1 ≤ x + m2 := fun x => by rw [hR, mem_filter]
    have mL1 : ∀ x, x ∈ L1 ↔ x ∈ L ∧ x < m1 := fun x => by rw [hL1, mem_filter]
    have mL2 : ∀ x, x ∈ L2 ↔ x ∈ L ∧ ¬ x < m1 := fun x => by rw [hL2, mem_filter]
    have mR1 : ∀ x, x ∈ R1 ↔ x ∈ R ∧ D + 1 ≤ x + m1 := fun x => by rw [hR1, mem_filter]
    have mR2 : ∀ x, x ∈ R2 ↔ x ∈ R ∧ ¬ D + 1 ≤ x + m1 := fun x => by rw [hR2, mem_filter]
    have mM : ∀ x, x ∈ Mm ↔ x ∈ A ∧ (z ≤ x ∧ x + z ≤ D) := fun x => by rw [hMm, mem_filter]
    have hLA : L ⊆ A := hL ▸ filter_subset _ _
    have hRA : R ⊆ A := hR ▸ filter_subset _ _
    have hMA : Mm ⊆ A := hMm ▸ filter_subset _ _
    have hL1L : L1 ⊆ L := hL1 ▸ filter_subset _ _
    have hL2L : L2 ⊆ L := hL2 ▸ filter_subset _ _
    have hR1R : R1 ⊆ R := hR1 ▸ filter_subset _ _
    have hR2R : R2 ⊆ R := hR2 ▸ filter_subset _ _
    have hdL : Disjoint L1 L2 := by rw [hL1, hL2]; exact disjoint_filter_filter_not _ _ _
    have hdR : Disjoint R1 R2 := by rw [hR1, hR2]; exact disjoint_filter_filter_not _ _ _
    have hcL : L1.card + L2.card = L.card := by
      rw [hL1, hL2]; exact card_filter_add_card_filter_not _
    have hcR : R1.card + R2.card = R.card := by
      rw [hR1, hR2]; exact card_filter_add_card_filter_not _
    have hcL' : L.card = Lc A m2 := by rw [hL]; rfl
    have hcR' : R.card = Rc A D m2 := by rw [hR]; rfl
    have hcL1 : L1.card = Lc A m1 := by
      rw [hL1, hL, filter_filter]; unfold Lc; congr 1; apply filter_congr; intro x _; omega
    have hcR1 : R1.card = Rc A D m1 := by
      rw [hR1, hR, filter_filter]; unfold Rc; congr 1; apply filter_congr; intro x _; omega
    have hGm2 : ((L.card : ℝ) + R.card) = ((G m2 : ℕ) : ℝ) := by
      rw [hcL', hcR', hGdef]; push_cast; ring
    have hGm1 : ((L1.card : ℝ) + R1.card) = ((G m1 : ℕ) : ℝ) := by
      rw [hcL1, hcR1, hGdef]; push_cast; ring
    have hGd : ((L2.card : ℝ) + R2.card) = ((G m2 : ℕ) : ℝ) - ((G m1 : ℕ) : ℝ) := by
      have e1 : (L1.card : ℝ) + L2.card = L.card := by exact_mod_cast hcL
      have e2 : (R1.card : ℝ) + R2.card = R.card := by exact_mod_cast hcR
      linarith
    have hdLR : Disjoint L R := by
      rw [disjoint_left]; intro x h1 h2; rw [mL] at h1; rw [mR] at h2; omega
    have hdML : Disjoint Mm L := by
      rw [disjoint_left]; intro x h1 h2; rw [mM] at h1; rw [mL] at h2; omega
    have hdMR : Disjoint Mm R := by
      rw [disjoint_left]; intro x h1 h2; rw [mM] at h1; rw [mR] at h2; omega
    -- pair sums
    have hSL := pair_sum_lb L L1 L2 T2 m1 m2 hL1L hL2L hdL
      (fun p hp => by
        rw [mem_prs] at hp; have := (mL _).1 hp.2.1; omega)
      (fun p hp => by
        rw [mem_prs] at hp; have := (mL1 _).1 hp.2.1; omega)
      (fun p hp => by
        rw [mem_prs] at hp
        have h1 := (mL2 _).1 hp.1; have h2 := (mL2 _).1 hp.2.1
        have h3 := (mL _).1 h2.1
        omega) hm12 hm2T2
    have hSR := pair_sum_lb R R1 R2 T2 m1 m2 hR1R hR2R hdR
      (fun p hp => by
        rw [mem_prs] at hp
        have h1 := (mR _).1 hp.1; have h2 := (mR _).1 hp.2.1
        have := hAD _ h2.1; omega)
      (fun p hp => by
        rw [mem_prs] at hp
        have h1 := (mR1 _).1 hp.1; have h2 := (mR1 _).1 hp.2.1
        have := hAD _ ((mR _).1 h2.1).1; omega)
      (fun p hp => by
        rw [mem_prs] at hp
        have h1 := (mR2 _).1 hp.1; have h2 := (mR2 _).1 hp.2.1
        have h3 := (mR _).1 h1.1
        omega) hm12 hm2T2
    have cv := prs_pair_lb L R
    have cv1 := prs_pair_lb L1 R1
    have cv2 := prs_pair_lb L2 R2
    rw [hGm2] at cv; rw [hGm1] at cv1; rw [hGd] at cv2
    obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ p ∈ prs L, ((T2 - (p.2 - p.1) : ℕ) : ℝ)
        + ∑ p ∈ prs R, ((T2 - (p.2 - p.1) : ℕ) : ℝ) := ⟨_, rfl⟩
    have hm12r : (m1 : ℝ) ≤ m2 := by exact_mod_cast hm12
    have hm2T2r : (m2 : ℝ) ≤ T2 := by exact_mod_cast hm2T2
    have hSraw : ((T2 : ℝ) - m2) * Qf ((G m2 : ℕ) : ℝ) + ((m2 : ℝ) - m1) * Qf ((G m1 : ℕ) : ℝ)
        + (m1 : ℝ) * Qf (((G m2 : ℕ) : ℝ) - ((G m1 : ℕ) : ℝ)) ≤ S := by
      have e1 := mul_le_mul_of_nonneg_left cv (by linarith : (0:ℝ) ≤ (T2 : ℝ) - m2)
      have e2 := mul_le_mul_of_nonneg_left cv1 (by linarith : (0:ℝ) ≤ (m2 : ℝ) - m1)
      have e3 := mul_le_mul_of_nonneg_left cv2 (Nat.cast_nonneg m1 : (0:ℝ) ≤ m1)
      rw [hSdef]; linarith
    obtain ⟨h1a, h2a⟩ := num_abig P a hk ha1
    have hm2X : (m2 : ℝ) - m1 ≤ Mid.card := by
      have : ((m2 - m1 : ℕ) : ℝ) ≤ Mid.card := by exact_mod_cast hcm2
      rwa [Nat.cast_sub hm12] at this
    have hm1Y : (m1 : ℝ) ≤ F.card := by exact_mod_cast hcm1
    have hSlb := S_lb a pα pβ T2 Mid.card F.card m1 m2 _ _ _ S hα0 hα1 hβ0 hβ1 ha0
      (Nat.cast_nonneg _) hm12r hm2T2r hm1Y hm2X (by rw [← hc2]; exact hl) (by rw [← hc1]; exact hl1)
      (by rw [← hc1, ← hc2]; exact hl2) h1a h2a hSraw
    -- core inequality on the middle set
    have hT2n : 1 ≤ T2 := by omega
    have hzD : 2 * z ≤ D := by omega
    have hMr' : ∀ x ∈ Mm, z ≤ x ∧ x ≤ z + (D - 2 * z) := fun x hx => by
      have := (mM x).1 hx; omega
    have hcM := core A Mm L R hA hMA hLA hRA hdML hdMR hdLR z (D - 2 * z) T2 hT2n hMr' ∅
      (empty_subset _)
    simp only [sum_empty, mul_zero, add_zero] at hcM
    rw [Nat.cast_sub hzD] at hcM
    push_cast at hcM
    rw [← hSdef] at hcM
    have hT2pos : (0 : ℝ) < T2 := by exact_mod_cast hT2n
    have hM'pos : (0 : ℝ) < (D : ℝ) - 2 * z + T2 := by
      have : (2 * z : ℝ) ≤ D := by exact_mod_cast hzD
      linarith
    have hMlb := M_lb ((D : ℝ) - 2 * z + T2) T2 Mm.card S hM'pos hT2pos (by
      have e : (D : ℝ) - 2 * z + T2 = (D : ℝ) - 2 * z + T2 := rfl
      linarith)
    -- size of the middle set
    have hc3' := card_three A D z hzD
    rw [← hMm, ← hkdef] at hc3'
    have hMcard : (Mm.card : ℝ) = k - ((G z : ℕ) : ℝ) := by
      have : (Lc A z : ℝ) + Rc A D z + Mm.card = k := by exact_mod_cast hc3'
      rw [hGdef]; push_cast; linarith
    have hκk : P ^ 2 - pμ * P - pc0 ≤ Mm.card := by
      rw [hMcard, hkP]
      have h1 : 2 * (1 + pα * pβ) * a ≤ 2 * (1 + pα * pβ) * (pτ * P + 2) :=
        mul_le_mul_of_nonneg_left ha2 (by positivity)
      have e : 2 * (1 + pα * pβ) * (pτ * P + 2) = pμ * P + pc0 := by
        unfold pμ pc0; ring
      rw [hc3] at hPz
      linarith
    have hMk : (Mm.card : ℝ) ≤ P ^ 2 := by
      rw [← hkP]; exact_mod_cast (hkdef ▸ card_le_card hMA)
    have hzr : (T : ℝ) - Mid.card - F.card ≤ z := by
      have : m2 + (T - z) ≤ F.card + Mid.card := hcz
      have h2 : ((T - z : ℕ) : ℝ) ≤ F.card + Mid.card := by
        have : T - z ≤ F.card + Mid.card := by omega
        exact_mod_cast this
      rw [Nat.cast_sub hzT] at h2
      linarith
    have hκ2 : (0 : ℝ) < pκ2 := by norm_num [pκ2, pα, pβ]
    have hSlb' : pτ₂ * T * (pκ2 ^ 2 * a ^ 2 - 3 * pκ2 * a)
        - a ^ 2 * (pcX * Mid.card + pcY * F.card) ≤ S := by
      rw [← hT2r]; simpa only [pκ2, pcX, pcY] using hSlb
    have hMlb' : (Mm.card : ℝ) ^ 2 * (1 - ((Mm.card : ℝ) - 1) / (pτ₂ * T) + 2 * S / (pτ₂ * T) ^ 2)
        ≤ D - 2 * z + pτ₂ * T := by
      rw [← hT2r]; exact hMlb
    exact realB_final P T a Mid.card F.card z Mm.card D S pτ pτ₂ pβ pδ pΛ pκ2 pcX pcY pKhi
      (P ^ 2 - pμ * P - pc0) _ hτpos hτ₂0 hβ0 hκ2 hP1 hT1 hT2 ha1 ha2 hMr hFr hcase.le hzr
      (num_kappa P hk) hκk hMk num_cX num_cY hSlb' hMlb' (num_hKhi P hk) num_hΛ1 num_hΛ2 num_hco
      (num_h3 P hk) (num_poly P hk)

lemma invert (u P : ℝ) (hu : 10 ^ 7 ≤ u) (hP : 0 ≤ P) (h : P ^ 4 - pb * P ^ 3 ≤ u ^ 4) :
    P ^ 2 ≤ u ^ 2 + 99703 / 100000 * u := by
  by_contra hlt; push_neg at hlt
  have h1 : (u + 498513 / 1000000) ^ 2 ≤ u ^ 2 + 99703 / 100000 * u := by nlinarith
  have h2 : u + 498513 / 1000000 < P := by
    by_contra h'; push_neg at h'
    have : P ^ 2 ≤ (u + 498513 / 1000000) ^ 2 := pow_le_pow_left₀ hP h' 2
    linarith
  have hug : 0 ≤ u + 498513 / 1000000 - pb := by unfold pb; linarith
  have h3 : (u + 498513 / 1000000) ^ 3 * (u + 498513 / 1000000 - pb) ≤ P ^ 3 * (P - pb) :=
    mul_le_mul (pow_le_pow_left₀ (by linarith) h2.le 3) (by linarith) hug (by positivity)
  have h4 : u ^ 4 < (u + 498513 / 1000000) ^ 3 * (u + 498513 / 1000000 - pb) := by
    rw [← sub_pos]
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ u = t + 10 ^ 7 := ⟨u - 10 ^ 7, by linarith, by ring⟩
    unfold pb; ring_nf; positivity
  have e : P ^ 3 * (P - pb) = P ^ 4 - pb * P ^ 3 := by ring
  linarith

theorem final_bound (N : ℕ) (hN : 10 ^ 28 ≤ N) :
    (h N : ℝ) ≤ Real.sqrt N + 0.99703 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
  change ((maxSidonSubsetCard (Finset.Icc 1 N) : ℕ) : ℝ) ≤ _
  unfold maxSidonSubsetCard
  obtain ⟨B, hB, hsup⟩ := exists_mem_eq_sup
    ((Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ))
    ⟨∅, by simp [IsSidon]⟩ Finset.card
  rw [hsup]
  rw [mem_filter, mem_powerset] at hB
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (N : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hu]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hu0 : 0 ≤ u := hu ▸ Real.rpow_nonneg hN0 _
  have hu4 : u ^ 4 = N := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hsq : Real.sqrt N = u ^ 2 := by
    rw [← hu4, show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq]
  have hu7 : 10 ^ 7 ≤ u := by
    by_contra hlt; push_neg at hlt
    have h1 : u ^ 4 < (10 ^ 7) ^ 4 := pow_lt_pow_left₀ hlt hu0 (by norm_num)
    have h2 : (10 : ℝ) ^ 28 ≤ N := by exact_mod_cast hN
    rw [hu4] at h1; norm_num at h1 h2; linarith
  by_cases hk : (10 ^ 7 : ℝ) ≤ Real.sqrt B.card
  · have hd := diam_bound B hB.2 N (fun a ha => (mem_Icc.1 (hB.1 ha)).2) hk
    have hinv := invert u (Real.sqrt B.card) hu7 (Real.sqrt_nonneg _) (by rw [hu4]; exact hd)
    rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hinv
    norm_num; linarith
  · push_neg at hk
    have h1 : (B.card : ℝ) < (10 ^ 7) ^ 2 := by
      rw [← Real.sq_sqrt (Nat.cast_nonneg B.card)]
      exact pow_lt_pow_left₀ hk (Real.sqrt_nonneg _) (by norm_num)
    have h2 : ((10 : ℝ) ^ 7) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu7 2
    have h3 : 0 ≤ 0.99703 * u := by positivity
    linarith

end OB
end Erdos30


/-- O'Bryant (2022): `h N ≤ √N + 0.99703 N^{1/4}` for all large `N`. -/
theorem solution : ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (Erdos30.h N : ℝ) ≤ Real.sqrt N + 0.99703 * (N : ℝ) ^ ((1 : ℝ) / 4) :=
  ⟨10 ^ 28, fun N hN => Erdos30.OB.final_bound N hN⟩
