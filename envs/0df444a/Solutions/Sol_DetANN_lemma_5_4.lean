-- Prove2me | solution 1 for DetANN.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T01:01:49.376293+00:00
-- url     : https://prove2.me/submissions/a1150f03-58e8-455c-8113-67a48b48bf46

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

/-- `α‖a + b‖² ≤ (1 + α)‖a‖² + α(1 + α)‖b‖²` for `α > 0` (from `‖a − αb‖² ≥ 0`). -/
lemma DetANNFinAux.norm_add_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (α : ℝ) :
    α * ‖a + b‖ ^ 2 ≤ (1 + α) * ‖a‖ ^ 2 + α * (1 + α) * ‖b‖ ^ 2 := by
  have h := norm_sub_sq_real a (α • b)
  have h0 : 0 ≤ ‖a - α • b‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real]
  rw [h, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h0
  nlinarith [h0]

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
    (Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖x v - xs‖ ^ 2 ≤ (1 + α) ^ 2 / (1 - τ) * ‖q - xs‖ ^ 2 := by
  have hd : 0 < d := d_pos S
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hα0 : 0 < α := by linarith
  have h1τ : 0 < 1 - τ := by linarith
  have hV : (0 : ℝ) < Fintype.card Vtx := by exact_mod_cast Fintype.card_pos
  have hO : (0 : ℝ) < Fintype.card Occ := by exact_mod_cast Fintype.card_pos
  -- per tuple: (1-τ)|Occ|/d ‖x_v - x⋆‖² ≤ ‖𝒜_v(x_v - x⋆)‖² ≤ (1+α)² ‖𝒜_v(q - x⋆)‖²
  have hper : ∀ v, (1 - τ) * Fintype.card Occ / d * ‖x v - xs‖ ^ 2 ≤
      (1 + α) ^ 2 * superNormSq A S v (q - xs) := by
    intro v
    have hlow : (1 - τ) * Fintype.card Occ / d * ‖x v - xs‖ ^ 2 ≤ superNormSq A S v (x v - xs) := by
      unfold superNormSq
      have : (1 - τ) * Fintype.card Occ / d * ‖x v - xs‖ ^ 2 =
          ∑ _o : Occ, (1 - τ) / d * ‖x v - xs‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      rw [this]
      exact Finset.sum_le_sum fun o _ => (hA.2 _ (hx v) _ hxs _).1
    have hup : α * superNormSq A S v (x v - xs) ≤
        (1 + α) * superNormSq A S v (q - x v) + α * (1 + α) * superNormSq A S v (q - xs) := by
      unfold superNormSq
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun o _ => ?_
      have e : x v - xs = -(q - x v) + (q - xs) := by abel
      have := norm_add_sq_le (A (S v o) (-(q - x v))) (A (S v o) (q - xs)) α
      rw [map_neg, norm_neg] at this
      rw [e, map_add, map_neg]
      exact this
    have hl := hloc v xs hxs
    have hsn : 0 ≤ superNormSq A S v (q - xs) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have : α * superNormSq A S v (x v - xs) ≤ α * ((1 + α) ^ 2 * superNormSq A S v (q - xs)) := by
      nlinarith
    have := le_of_mul_le_mul_left this hα0
    linarith
  -- average over v
  have hsum : ∑ v, superNormSq A S v (q - xs) =
      ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ) / d * ‖q - xs‖ ^ 2 := by
    rw [← sum_pairs_parseval A hA.1 S hS, Fintype.sum_prod_type]; rfl
  have htot : (1 - τ) * Fintype.card Occ / d * ∑ v, ‖x v - xs‖ ^ 2 ≤
      (1 + α) ^ 2 * (((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ) / d * ‖q - xs‖ ^ 2) := by
    rw [Finset.mul_sum, ← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => hper v
  push_cast at htot
  rw [div_mul_eq_mul_div, inv_mul_le_iff₀ hV, mul_div_assoc', le_div_iff₀ h1τ]
  have e : (1 - τ) * Fintype.card Occ / d * ∑ v, ‖x v - xs‖ ^ 2 =
      (Fintype.card Occ / d) * ((∑ v, ‖x v - xs‖ ^ 2) * (1 - τ)) := by ring
  have e2 : (1 + α) ^ 2 * ((Fintype.card Vtx : ℝ) * Fintype.card Occ / d * ‖q - xs‖ ^ 2) =
      (Fintype.card Occ / d) * (Fintype.card Vtx * ((1 + α) ^ 2 * ‖q - xs‖ ^ 2)) := by ring
  rw [e, e2] at htot
  exact le_of_mul_le_mul_left htot (by positivity)
