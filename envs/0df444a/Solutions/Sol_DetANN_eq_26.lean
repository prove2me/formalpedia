-- Prove2me | solution 1 for DetANN.eq_26
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T01:01:47.668072+00:00
-- url     : https://prove2.me/submissions/49759303-0c41-4970-b939-66c1a59150e8

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_TupleFamily

set_option linter.unusedSectionVars false

namespace DetANNFinAux

open DetANN

section general
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}

/-- Finite bias–variance: `∑_{p∈s} ‖u − z_p‖² = |s|·‖u − m‖² + ∑_{p∈s} ‖z_p − m‖²`, `m` the mean. -/
lemma sum_sq_dev (s : Finset ι) (z : ι → E) (u : E) :
    ∑ p ∈ s, ‖u - z p‖ ^ 2 = s.card * ‖u - (s.card : ℝ)⁻¹ • ∑ p ∈ s, z p‖ ^ 2 +
      ∑ p ∈ s, ‖z p - (s.card : ℝ)⁻¹ • ∑ p ∈ s, z p‖ ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  set m := (s.card : ℝ)⁻¹ • ∑ p ∈ s, z p
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hsum : ∑ p ∈ s, (z p - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ hc, one_smul, sub_self]
  have hpt : ∀ p, ‖u - z p‖ ^ 2 = ‖u - m‖ ^ 2 - 2 * inner ℝ (u - m) (z p - m) + ‖z p - m‖ ^ 2 := by
    intro p
    have : u - z p = (u - m) - (z p - m) := by abel
    rw [this, norm_sub_sq_real]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← inner_sum, hsum,
    inner_zero_right, Finset.sum_const, nsmul_eq_mul]
  ring

/-- `∑_{p,p'∈s} ‖z_p − z_{p'}‖² = 2|s| ∑_{p∈s} ‖z_p − m‖²`. -/
lemma sum_pair_sq (s : Finset ι) (z : ι → E) :
    ∑ p ∈ s, ∑ p' ∈ s, ‖z p - z p'‖ ^ 2 =
      2 * s.card * ∑ p ∈ s, ‖z p - (s.card : ℝ)⁻¹ • ∑ p ∈ s, z p‖ ^ 2 := by
  simp_rw [sum_sq_dev s z]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

end general

variable {d b : ℕ} {Vtx Occ : Type} [Fintype Vtx] [Fintype Occ]

/-- The fiber of block `i`. -/
abbrev fib (S : Vtx → Occ → Fin d) (i : Fin d) : Finset (Vtx × Occ) :=
  Finset.univ.filter fun p : Vtx × Occ => S p.1 p.2 = i

lemma card_fib (S : Vtx → Occ → Fin d) (i : Fin d) : (fib S i).card = blockCount S i := rfl

lemma condMean_eq (S : Vtx → Occ → Fin d) (x : Vtx → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    condMean S x xs i = ((fib S i).card : ℝ)⁻¹ • ∑ p ∈ fib S i, (x p.1 - xs) := rfl

/-- Sum over pairs, regrouped by the block. -/
lemma sum_by_fib {M : Type*} [AddCommMonoid M] (S : Vtx → Occ → Fin d)
    (f : Vtx × Occ → Fin d → M) :
    ∑ p : Vtx × Occ, f p (S p.1 p.2) = ∑ i, ∑ p ∈ fib S i, f p i := by
  rw [← Finset.sum_fiberwise Finset.univ (fun p : Vtx × Occ => S p.1 p.2)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.1 hp).2]

/-- Under uniform frequencies with `Vtx, Occ` nonempty: `d > 0` and `blockCount = M/d`. -/
lemma d_pos [Nonempty Vtx] [Nonempty Occ] (S : Vtx → Occ → Fin d) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; exact (S (Classical.arbitrary _) (Classical.arbitrary _)).elim0
  · exact h

lemma blockCount_real [Nonempty Vtx] [Nonempty Occ] (S : Vtx → Occ → Fin d) (hS : UniformFreq S)
    (i : Fin d) :
    (blockCount S i : ℝ) = ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ) / d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (d_pos S).ne'
  rw [eq_div_iff hd]; exact_mod_cast hS i

lemma M_pos [Nonempty Vtx] [Nonempty Occ] :
    (0 : ℝ) < ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ) := by
  have := Fintype.card_pos (α := Vtx); have := Fintype.card_pos (α := Occ); positivity

/-- `∑_{(v,o)} ‖A_{S v o} z‖² = (M/d)·‖z‖²` (uniform frequencies and Parseval). -/
lemma sum_pairs_parseval [Nonempty Vtx] [Nonempty Occ]
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (hpar : ∀ z : EuclideanSpace ℝ (Fin d), ∑ i, ‖A i z‖ ^ 2 = ‖z‖ ^ 2)
    (S : Vtx → Occ → Fin d) (hS : UniformFreq S) (z : EuclideanSpace ℝ (Fin d)) :
    ∑ p : Vtx × Occ, ‖A (S p.1 p.2) z‖ ^ 2 =
      ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ) / d * ‖z‖ ^ 2 := by
  rw [sum_by_fib S (fun _ i => ‖A i z‖ ^ 2)]
  simp_rw [Finset.sum_const, nsmul_eq_mul, card_fib, blockCount_real S hS]
  rw [← Finset.mul_sum, hpar]

end DetANNFinAux

open DetANN DetANNFinAux in
theorem solution {d b : ℕ} {Vtx Occ : Type} [Fintype Vtx] [Fintype Occ] [Nonempty Vtx] [Nonempty Occ]
    (τ α : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα : 1 ≤ α)
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (hA : IsBalancedBlockSystem τ P A)
    (S : Vtx → Occ → Fin d) (hS : UniformFreq S)
    (q xs : EuclideanSpace ℝ (Fin d)) (hxs : xs ∈ P)
    (x : Vtx → EuclideanSpace ℝ (Fin d)) (hx : ∀ v, x v ∈ P)
    (hloc : LocalGuarantee A S P q x α) :
    ∑ i, ‖A i (q - xs - condMean S x xs i)‖ ^ 2 + (1 - τ) * withinVar S x xs ≤
        α ^ 2 * ‖q - xs‖ ^ 2 ∧
      withinVar S x xs ≤ α ^ 2 * ‖q - xs‖ ^ 2 / (1 - τ) ∧
      ∑ i, ‖A i (q - xs - condMean S x xs i)‖ ^ 2 + withinVar S x xs ≤
        α ^ 2 * ‖q - xs‖ ^ 2 / (1 - τ) := by
  have hd : 0 < d := d_pos S
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set M : ℝ := ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ) with hMdef
  have hM : 0 < M := M_pos
  set w := q - xs
  set y : Vtx → EuclideanSpace ℝ (Fin d) := fun v => x v - xs
  set a := condMean S x xs
  set T := ∑ i, ‖A i (w - a i)‖ ^ 2
  set 𝒱 := withinVar S x xs
  -- (i) the local guarantee against `x⋆`, summed over tuples
  have hupper : ∑ p : Vtx × Occ, ‖A (S p.1 p.2) (w - y p.1)‖ ^ 2 ≤ α ^ 2 * (M / d * ‖w‖ ^ 2) := by
    rw [← sum_pairs_parseval A hA.1 S hS w, Finset.mul_sum, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun v _ => ?_
    have := hloc v xs hxs
    simp only [superNormSq] at this
    rw [← Finset.mul_sum]
    have e : w - y v = q - x v := by simp [w, y]
    simp only [e]
    exact this
  -- (ii) the same sum, decomposed fiberwise
  have hfib : ∀ i, ∑ p ∈ fib S i, ‖A i (w - y p.1)‖ ^ 2 ≥
      (fib S i).card * ‖A i (w - a i)‖ ^ 2 +
        (1 - τ) / d * ∑ p ∈ fib S i, ‖y p.1 - a i‖ ^ 2 := by
    intro i
    have hlin : A i (a i) = ((fib S i).card : ℝ)⁻¹ • ∑ p ∈ fib S i, A i (y p.1) := by
      simp [a, condMean_eq, map_sum, y]
    have h1 := sum_sq_dev (fib S i) (fun p => A i (y p.1)) (A i w)
    rw [← hlin] at h1
    simp only [map_sub] at h1 ⊢
    rw [h1, map_sub]
    gcongr
    -- within-fiber variance: projected ≥ (1-τ)/d · original, via the pair form
    rcases (fib S i).eq_empty_or_nonempty with he | hne
    · simp [he]
    have hc : (0 : ℝ) < (fib S i).card := by exact_mod_cast hne.card_pos
    have p1 := sum_pair_sq (fib S i) (fun p => A i (y p.1))
    have p2 := sum_pair_sq (fib S i) (fun p => y p.1)
    rw [← hlin] at p1
    have hcmp : (1 - τ) / d * ∑ p ∈ fib S i, ∑ p' ∈ fib S i, ‖y p.1 - y p'.1‖ ^ 2 ≤
        ∑ p ∈ fib S i, ∑ p' ∈ fib S i, ‖A i (y p.1) - A i (y p'.1)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p' _ => ?_
      have e : y p.1 - y p'.1 = x p.1 - x p'.1 := by simp [y]
      rw [← map_sub, e]
      exact (hA.2 _ (hx _) _ (hx _) i).1
    rw [p1, p2] at hcmp
    have : (2 * (fib S i).card) * ((1 - τ) / d * ∑ p ∈ fib S i, ‖y p.1 - a i‖ ^ 2) ≤
        (2 * (fib S i).card) * ∑ p ∈ fib S i, ‖A i (y p.1) - A i (a i)‖ ^ 2 := by
      simp only [a, condMean_eq] at hcmp ⊢
      linarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hsplit : ∑ p : Vtx × Occ, ‖A (S p.1 p.2) (w - y p.1)‖ ^ 2 ≥
      M / d * T + (1 - τ) / d * (M * 𝒱) := by
    rw [sum_by_fib S (fun p i => ‖A i (w - y p.1)‖ ^ 2)]
    have hW : M * 𝒱 = ∑ i, ∑ p ∈ fib S i, ‖y p.1 - a i‖ ^ 2 := by
      simp only [𝒱, withinVar]
      rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul,
        sum_by_fib S (fun p i => ‖x p.1 - xs - condMean S x xs i‖ ^ 2)]
    rw [hW, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hfib i
    rw [card_fib, blockCount_real S hS] at this
    exact this
  -- (iii) combine
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h𝒱0 : 0 ≤ 𝒱 := by
    simp only [𝒱, withinVar]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hmain : T + (1 - τ) * 𝒱 ≤ α ^ 2 * ‖w‖ ^ 2 := by
    have h := hsplit.le.trans hupper
    have e : M / d * T + (1 - τ) / d * (M * 𝒱) = (M / d) * (T + (1 - τ) * 𝒱) := by ring
    have e2 : α ^ 2 * (M / d * ‖w‖ ^ 2) = (M / d) * (α ^ 2 * ‖w‖ ^ 2) := by ring
    rw [e, e2] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have h1τ : 0 < 1 - τ := by linarith
  refine ⟨hmain, ?_, ?_⟩
  · rw [le_div_iff₀ h1τ]; nlinarith
  · rw [le_div_iff₀ h1τ]; nlinarith
