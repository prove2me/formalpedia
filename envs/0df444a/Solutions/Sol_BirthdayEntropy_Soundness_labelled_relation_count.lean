-- Prove2me | solution 1 for BirthdayEntropy.Soundness.labelled_relation_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:49:50.228147+00:00
-- url     : https://prove2.me/submissions/b01d9cc5-b0f2-421b-9856-0731a394891a

import Mathlib
noncomputable section
open scoped Classical
open Finset

private def av {V : Type*} [Fintype V] (f : V → ℝ) : ℝ := (∑ v, f v) / Fintype.card V

private lemma av_nonneg {V : Type*} [Fintype V] (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) :
    0 ≤ av f := div_nonneg (Finset.sum_nonneg (fun v _ => hf v)) (by positivity)

private lemma av_mono {V : Type*} [Fintype V] {f g : V → ℝ} (h : ∀ v, f v ≤ g v) :
    av f ≤ av g := div_le_div_of_nonneg_right (Finset.sum_le_sum (fun v _ => h v)) (by positivity)

private lemma av_pow {V : Type*} [Fintype V] [Nonempty V] (f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v) (r : ℕ) : (av f)^r ≤ av (fun v => (f v)^r) := by
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ : V => 1 / (Fintype.card V : ℝ)) f
    (by intros; positivity) (by simp [Fintype.card_ne_zero]) (fun v _ => hf v) r
  simpa [av, div_eq_mul_inv, ← Finset.sum_mul, mul_comm] using h

private lemma av_pi {V : Type*} [Fintype V] (f : V → ℝ) (r : ℕ) :
    av (fun X : Fin r → V => ∏ i, f (X i)) = (av f)^r := by
  simp only [av, ← Fintype.sum_pow, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_pow]

private lemma av_comm {U V : Type*} [Fintype U] [Fintype V] (f : U → V → ℝ) :
    av (fun u => av (fun v => f u v)) = av (fun v => av (fun u => f u v)) := by
  simp only [av, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm]
  congr 1
  ring

private lemma av_pair {U V : Type*} [Fintype U] [Fintype V] (f : U → V → ℝ) :
    av (fun x : U × V => f x.1 x.2) = av (fun u => av (fun v => f u v)) := by
  simp [av, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div, div_div, mul_comm]

private lemma matrix_biclique {V : Type*} [Fintype V] [Nonempty V]
    (f : V → V → ℝ) (hf : ∀ u v, 0 ≤ f u v) (r : ℕ) :
    (av (fun z : V × V => f z.1 z.2))^(r*r) ≤
      av (fun z : (Fin r → V) × (Fin r → V) => ∏ i, ∏ j, f (z.1 i) (z.2 j)) := by
  let h : (Fin r → V) → ℝ := fun L => av (fun v => ∏ i, f (L i) v)
  have hh : ∀ L, 0 ≤ h L := fun L => av_nonneg _ (fun v => Finset.prod_nonneg (fun i _ => hf _ _))
  have hbase : (av (fun z : V × V => f z.1 z.2))^r ≤ av h := by
    rw [av_pair, av_comm f]
    calc
      _ ≤ av (fun v => (av (fun u => f u v))^r) := av_pow _ (fun v => av_nonneg _ (fun u => hf u v)) r
      _ = av h := by
        simp only [h]
        rw [av_comm]
        congr 1
        funext v
        exact (av_pi _ r).symm
  have hend : av (fun L => (h L)^r) =
      av (fun z : (Fin r → V) × (Fin r → V) => ∏ i, ∏ j, f (z.1 i) (z.2 j)) := by
    rw [av_pair (fun L R : Fin r → V => ∏ i, ∏ j, f (L i) (R j))]
    congr 1
    funext L
    rw [← av_pi]
    congr 1
    funext R
    rw [Finset.prod_comm]
  calc
    _ = ((av (fun z : V × V => f z.1 z.2))^r)^r := by rw [← pow_mul]
    _ ≤ (av h)^r := pow_le_pow_left₀ (pow_nonneg (av_nonneg _ (fun z => hf _ _)) r) hbase r
    _ ≤ av (fun L => (h L)^r) := av_pow h hh r
    _ = _ := hend

theorem solution {V : Type*} [Fintype V] [Nonempty V] (R : V → V → Prop) (r : ℕ) :
    (((Finset.univ.filter (fun z : V × V => R z.1 z.2)).card : ℝ) /
      (Fintype.card V : ℝ)^2)^(r*r) ≤
    ((Finset.univ.filter (fun z : (Fin r → V) × (Fin r → V) =>
      ∀ i j, R (z.1 i) (z.2 j))).card : ℝ) / (Fintype.card V : ℝ)^(2*r) := by
  classical
  have h := matrix_biclique (fun u v => if R u v then 1 else 0) (by intros; split_ifs <;> norm_num) r
  have hind (z : (Fin r → V) × (Fin r → V)) :
      (∏ i, ∏ j, if R (z.1 i) (z.2 j) then (1 : ℝ) else 0) =
      if ∀ i j, R (z.1 i) (z.2 j) then 1 else 0 := by
    by_cases hz : ∀ i j, R (z.1 i) (z.2 j)
    · simp [hz]
    · obtain ⟨i,hi⟩ := not_forall.mp hz
      obtain ⟨j,hij⟩ := not_forall.mp hi
      rw [if_neg hz]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hij)
  simp_rw [hind] at h
  simpa [av, Fintype.card_prod, Fintype.card_fun, Nat.cast_mul, Nat.cast_pow, ← pow_two, ← pow_mul, Nat.mul_comm] using h
