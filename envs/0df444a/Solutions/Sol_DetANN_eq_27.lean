-- Prove2me | solution 1 for DetANN.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T01:04:19.987621+00:00
-- url     : https://prove2.me/submissions/e41c840d-c5f2-44fb-a8e0-b8f9ca56f268

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_TupleFamily
import Theorems.Thm_DetANN_eq_26
import Theorems.Thm_DetANN_lemma_5_3
import Theorems.Thm_DetANN_lemma_5_4

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
    (hloc : LocalGuarantee A S P q x α)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκV : betweenVar S x xs ≤ κ * withinVar S x xs) :
    Real.sqrt ((Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖q - x v‖ ^ 2) ≤
        (α + Real.sqrt (2 * α ^ 2 * κ + 12 * τ * (1 + α) ^ 2)) / Real.sqrt (1 - τ) * ‖q - xs‖ ∧
      ∃ v : Vtx, ‖q - x v‖ ≤
        (α + Real.sqrt (2 * α ^ 2 * κ + 12 * τ * (1 + α) ^ 2)) / Real.sqrt (1 - τ) * ‖q - xs‖ := by
  -- the three milestone inputs
  obtain ⟨-, h26b, h26c⟩ := eq_26 τ α hτ0 hτ1 hα P A hA S hS q xs hxs x hx hloc
  have h53 := lemma_5_3 τ hτ0 hτ1 P A hA S hS q xs hxs x hx
  have h54 := lemma_5_4 τ α hτ0 hτ1 hα P A hA S hS q xs hxs x hx hloc
  -- notation
  have h1τ : 0 < 1 - τ := by linarith
  have hV : (0 : ℝ) < Fintype.card Vtx := by exact_mod_cast Fintype.card_pos
  have hO : (0 : ℝ) < Fintype.card Occ := by exact_mod_cast Fintype.card_pos
  set M : ℝ := ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ) with hMdef
  have hM : 0 < M := M_pos
  set w := q - xs
  set y : Vtx → EuclideanSpace ℝ (Fin d) := fun v => x v - xs
  set a := mean x xs
  set ai := condMean S x xs
  set T := ∑ i, ‖A i (w - ai i)‖ ^ 2
  set U := ∑ i, ‖A i (ai i - a)‖ ^ 2
  set 𝒱 := withinVar S x xs
  set B := betweenVar S x xs
  set E := (Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖x v - xs‖ ^ 2
  set R := ‖w‖ ^ 2 / (1 - τ)
  set s := Real.sqrt (2 * α ^ 2 * κ + 12 * τ * (1 + α) ^ 2)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h𝒱0 : 0 ≤ 𝒱 := by
    simp only [𝒱, withinVar]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hR0 : 0 ≤ R := by positivity
  have hα0 : 0 ≤ α := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- (a) E_V ‖q − x_V‖² = ‖w − a‖² + E_V ‖y_V − a‖²
  have hstep1 : (Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖q - x v‖ ^ 2 =
      ‖w - a‖ ^ 2 + (Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖y v - a‖ ^ 2 := by
    have h := sum_sq_dev (Finset.univ : Finset Vtx) y w
    have ha : ((Finset.univ : Finset Vtx).card : ℝ)⁻¹ • ∑ p ∈ (Finset.univ : Finset Vtx), y p = a := by
      simp [a, mean, y, Finset.card_univ]
    rw [ha] at h
    have e : ∀ v, q - x v = w - y v := fun v => by simp [w, y]
    simp_rw [e]
    rw [h, Finset.card_univ]
    field_simp
  -- (b) E_V ‖y_V − a‖² = 𝒱 + B (the law of total variance over (V, I))
  have hstep2 : (Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖y v - a‖ ^ 2 = 𝒱 + B := by
    have hpairs : ∑ p : Vtx × Occ, ‖y p.1 - a‖ ^ 2 = Fintype.card Occ * ∑ v, ‖y v - a‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      simp
    have hfib : ∑ p : Vtx × Occ, ‖y p.1 - a‖ ^ 2 =
        ∑ p : Vtx × Occ, ‖ai (S p.1 p.2) - a‖ ^ 2 +
          ∑ p : Vtx × Occ, ‖x p.1 - xs - ai (S p.1 p.2)‖ ^ 2 := by
      rw [sum_by_fib S (fun p _ => ‖y p.1 - a‖ ^ 2), sum_by_fib S (fun _ i => ‖ai i - a‖ ^ 2),
        sum_by_fib S (fun p i => ‖x p.1 - xs - ai i‖ ^ 2), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := sum_sq_dev (fib S i) (fun p => y p.1) a
      have hm : ((fib S i).card : ℝ)⁻¹ • ∑ p ∈ fib S i, y p.1 = ai i := by
        simp [ai, condMean_eq, y]
      rw [hm] at h
      simp_rw [norm_sub_rev (y _) a, h, norm_sub_rev a (ai i), Finset.sum_const, nsmul_eq_mul]
      rfl
    have h𝒱 : 𝒱 = M⁻¹ * ∑ p : Vtx × Occ, ‖x p.1 - xs - ai (S p.1 p.2)‖ ^ 2 := rfl
    have hB : B = M⁻¹ * ∑ p : Vtx × Occ, ‖ai (S p.1 p.2) - a‖ ^ 2 := rfl
    rw [h𝒱, hB, add_comm (M⁻¹ * _) (M⁻¹ * _), ← mul_add, ← hfib, hpairs, hMdef]
    push_cast
    field_simp
  -- (c) ‖w − a‖² ≤ T + 2√T√U + U  (Parseval and Cauchy–Schwarz)
  have hstep3 : ‖w - a‖ ^ 2 ≤ T + 2 * (Real.sqrt T * Real.sqrt U) + U := by
    rw [← hA.1]
    have e : ∀ i, A i (w - a) = A i (w - ai i) + A i (ai i - a) := fun i => by
      rw [← map_add]; congr 1; abel
    simp_rw [e, norm_add_sq_real]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have cs : ∑ i, inner ℝ (A i (w - ai i)) (A i (ai i - a)) ≤ Real.sqrt T * Real.sqrt U := by
      calc ∑ i, inner ℝ (A i (w - ai i)) (A i (ai i - a))
          ≤ ∑ i, ‖A i (w - ai i)‖ * ‖A i (ai i - a)‖ :=
            Finset.sum_le_sum fun i _ => real_inner_le_norm _ _
        _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    linarith
  -- (d) the bounds from the milestones
  have hTV : T + 𝒱 ≤ α ^ 2 * R := by simpa [mul_div_assoc] using h26c
  have h𝒱R : 𝒱 ≤ α ^ 2 * R := by simpa [mul_div_assoc] using h26b
  have hER : E ≤ (1 + α) ^ 2 * R := by
    have : (1 + α) ^ 2 / (1 - τ) * ‖q - xs‖ ^ 2 = (1 + α) ^ 2 * R := by simp only [R, w]; ring
    linarith
  have hs2 : s ^ 2 = 2 * α ^ 2 * κ + 12 * τ * (1 + α) ^ 2 := Real.sq_sqrt (by positivity)
  have hUB : U + B ≤ s ^ 2 * R := by
    rw [hs2]
    have : B ≤ κ * (α ^ 2 * R) := hκV.trans (mul_le_mul_of_nonneg_left h𝒱R hκ)
    nlinarith
  have hU : U ≤ s ^ 2 * R := by
    have : 0 ≤ B := by
      simp only [B, betweenVar]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  have hsqT : Real.sqrt T ≤ α * Real.sqrt R := by
    rw [← Real.sqrt_sq hα0, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqU : Real.sqrt U ≤ s * Real.sqrt R := by
    rw [← Real.sqrt_sq hs0, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hU
  have hRR : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR0
  have hmain : (Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖q - x v‖ ^ 2 ≤ (α + s) ^ 2 * R := by
    rw [hstep1, hstep2]
    have hprod : Real.sqrt T * Real.sqrt U ≤ α * s * R := by
      calc Real.sqrt T * Real.sqrt U ≤ (α * Real.sqrt R) * (s * Real.sqrt R) :=
            mul_le_mul hsqT hsqU (Real.sqrt_nonneg _) (by positivity)
        _ = α * s * (Real.sqrt R * Real.sqrt R) := by ring
        _ = α * s * R := by rw [hRR]
    nlinarith
  -- (e) take square roots
  have hbound : (α + s) / Real.sqrt (1 - τ) * ‖w‖ = Real.sqrt ((α + s) ^ 2 * R) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_div' _ h1τ.le,
      Real.sqrt_sq (norm_nonneg _)]
    ring
  have part1 : Real.sqrt ((Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖q - x v‖ ^ 2) ≤
      (α + s) / Real.sqrt (1 - τ) * ‖w‖ := by
    rw [hbound]; exact Real.sqrt_le_sqrt hmain
  refine ⟨part1, ?_⟩
  -- (f) some tuple is at most the root mean square
  set β := (α + s) / Real.sqrt (1 - τ) * ‖w‖
  have hβ0 : 0 ≤ β := by positivity
  have hsum : ∑ v, ‖q - x v‖ ^ 2 ≤ ∑ _v : Vtx, β ^ 2 := by
    have h := (Real.sqrt_le_left hβ0).mp part1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [inv_mul_le_iff₀ hV] at h
    exact h
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨v, (sq_le_sq₀ (norm_nonneg _) hβ0).mp hv⟩
