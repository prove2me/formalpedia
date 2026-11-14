-- Prove2me | solution 1 for DetANN.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T01:01:48.657439+00:00
-- url     : https://prove2.me/submissions/9970ebeb-1e13-4585-8c29-a230612b0aeb

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

namespace DetANNFinAux

section quad
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {ι : Type*} [Fintype ι]

/-- Polarization: if `‖A z‖² = κ‖z‖² ± τκ‖z‖²` on all `y_v` and all differences `y_v − y_{v'}`, then
`‖A(∑ λ_v y_v)‖² ≤ κ‖∑ λ_v y_v‖² + 3τκ (∑|λ_v|)(∑ |λ_v| ‖y_v‖²)`. -/
lemma quad_bound (A : E →ₗ[ℝ] F) (κ τ : ℝ) (hκτ : 0 ≤ τ * κ) (y : ι → E) (c : ι → ℝ)
    (h1 : ∀ v, |‖A (y v)‖ ^ 2 - κ * ‖y v‖ ^ 2| ≤ τ * κ * ‖y v‖ ^ 2)
    (h2 : ∀ v v', |‖A (y v - y v')‖ ^ 2 - κ * ‖y v - y v'‖ ^ 2| ≤ τ * κ * ‖y v - y v'‖ ^ 2) :
    ‖A (∑ v, c v • y v)‖ ^ 2 ≤ κ * ‖∑ v, c v • y v‖ ^ 2 +
      3 * (τ * κ) * ((∑ v, |c v|) * ∑ v, |c v| * ‖y v‖ ^ 2) := by
  set G : ι → ι → ℝ := fun v v' => inner ℝ (A (y v)) (A (y v')) - κ * inner ℝ (y v) (y v')
  have hG : ∀ v v', |G v v'| ≤ (3 / 2) * (τ * κ) * (‖y v‖ ^ 2 + ‖y v'‖ ^ 2) := by
    intro v v'
    have e1 := norm_sub_sq_real (A (y v)) (A (y v'))
    have e2 := norm_sub_sq_real (y v) (y v')
    rw [← map_sub] at e1
    have hG2 : 2 * G v v' = (‖A (y v)‖ ^ 2 - κ * ‖y v‖ ^ 2) + (‖A (y v')‖ ^ 2 - κ * ‖y v'‖ ^ 2)
        - (‖A (y v - y v')‖ ^ 2 - κ * ‖y v - y v'‖ ^ 2) := by
      simp only [G]; rw [e1, e2]; ring
    have hd : ‖y v - y v'‖ ^ 2 ≤ 2 * ‖y v‖ ^ 2 + 2 * ‖y v'‖ ^ 2 := by
      have := norm_sub_le (y v) (y v')
      nlinarith [norm_nonneg (y v - y v'), norm_nonneg (y v), norm_nonneg (y v'),
        sq_nonneg (‖y v‖ - ‖y v'‖)]
    have a1 := h1 v; have a2 := h1 v'; have a3 := h2 v v'
    rw [abs_le] at a1 a2 a3 ⊢
    constructor <;> nlinarith
  have expand : ‖A (∑ v, c v • y v)‖ ^ 2 - κ * ‖∑ v, c v • y v‖ ^ 2 =
      ∑ v, ∑ v', c v * c v' * G v v' := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, map_sum]
    simp only [map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, G,
      RCLike.conj_to_real, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => ?_
    rw [real_inner_comm (A (y v)) (A (y v')), real_inner_comm (y v) (y v')]
    ring
  have bound : ∑ v, ∑ v', c v * c v' * G v v' ≤
      ∑ v, ∑ v', |c v| * |c v'| * ((3 / 2) * (τ * κ) * (‖y v‖ ^ 2 + ‖y v'‖ ^ 2)) := by
    refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun v' _ => ?_
    calc c v * c v' * G v v' ≤ |c v * c v' * G v v'| := le_abs_self _
      _ = |c v| * |c v'| * |G v v'| := by rw [abs_mul, abs_mul]
      _ ≤ _ := by gcongr; exact hG v v'
  have eval : ∑ v, ∑ v', |c v| * |c v'| * ((3 / 2) * (τ * κ) * (‖y v‖ ^ 2 + ‖y v'‖ ^ 2)) =
      3 * (τ * κ) * ((∑ v, |c v|) * ∑ v, |c v| * ‖y v‖ ^ 2) := by
    set k := (3 / 2) * (τ * κ)
    have e1 : ∑ v, ∑ v', k * ((|c v| * ‖y v‖ ^ 2) * |c v'|) =
        k * ((∑ v, |c v| * ‖y v‖ ^ 2) * ∑ v, |c v|) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]; simp_rw [Finset.mul_sum]
    have e2 : ∑ v, ∑ v', k * (|c v| * (|c v'| * ‖y v'‖ ^ 2)) =
        k * ((∑ v, |c v|) * ∑ v, |c v| * ‖y v‖ ^ 2) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]; simp_rw [Finset.mul_sum]
    have : ∀ v v', |c v| * |c v'| * (k * (‖y v‖ ^ 2 + ‖y v'‖ ^ 2)) =
        k * ((|c v| * ‖y v‖ ^ 2) * |c v'|) + k * (|c v| * (|c v'| * ‖y v'‖ ^ 2)) := by
      intros; ring
    simp_rw [this, Finset.sum_add_distrib]
    rw [e1, e2]; ring
  linarith
end quad

end DetANNFinAux

open DetANN DetANNFinAux in
theorem solution {d b : ℕ} {Vtx Occ : Type} [Fintype Vtx] [Fintype Occ] [Nonempty Vtx] [Nonempty Occ]
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (hA : IsBalancedBlockSystem τ P A)
    (S : Vtx → Occ → Fin d) (hS : UniformFreq S)
    (q xs : EuclideanSpace ℝ (Fin d)) (hxs : xs ∈ P)
    (x : Vtx → EuclideanSpace ℝ (Fin d)) (hx : ∀ v, x v ∈ P) :
    ∑ i, ‖A i (condMean S x xs i - mean x xs)‖ ^ 2 ≤
      betweenVar S x xs + 12 * τ * ((Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖x v - xs‖ ^ 2) := by
  have hd : 0 < d := d_pos S
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set M : ℝ := ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ) with hMdef
  have hM : 0 < M := M_pos
  have hV : (0 : ℝ) < Fintype.card Vtx := by exact_mod_cast Fintype.card_pos
  set y : Vtx → EuclideanSpace ℝ (Fin d) := fun v => x v - xs
  -- occurrence counts and weights
  set n : Fin d → Vtx → ℝ := fun i v => ((Finset.univ.filter fun o => S v o = i).card : ℝ)
  set cnt : Fin d → ℝ := fun i => (blockCount S i : ℝ)
  have hcnt : ∀ i, cnt i = M / d := fun i => blockCount_real S hS i
  have hcpos : ∀ i, 0 < cnt i := fun i => by rw [hcnt]; positivity
  set lam : Fin d → Vtx → ℝ := fun i v => n i v / cnt i - (Fintype.card Vtx : ℝ)⁻¹
  have hfibsum : ∀ i (f : Vtx → EuclideanSpace ℝ (Fin d)),
      ∑ p ∈ fib S i, f p.1 = ∑ v, n i v • f v := by
    intro i f
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_filter]
    simp [n, Nat.cast_smul_eq_nsmul]
  have hn_sum : ∀ i, ∑ v, n i v = cnt i := by
    intro i
    simp only [n, cnt, blockCount]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_filter]; push_cast; rfl
  have hn_sum_i : ∀ v, ∑ i, n i v = Fintype.card Occ := by
    intro v
    simp only [n]
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset Occ))
      (t := (Finset.univ : Finset (Fin d))) (f := S v) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at this
    exact_mod_cast this.symm
  have hu : ∀ i, condMean S x xs i - mean x xs = ∑ v, lam i v • y v := by
    intro i
    rw [condMean_eq, card_fib, hfibsum i y]
    simp only [mean]
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [lam, y, cnt]
    module
  -- the balance bounds in the form needed by `quad_bound`, κ = 1/d
  have hbal : ∀ z, (∃ u ∈ P, ∃ u' ∈ P, z = u - u') → ∀ i,
      |‖A i z‖ ^ 2 - (1 / d) * ‖z‖ ^ 2| ≤ τ * (1 / d) * ‖z‖ ^ 2 := by
    rintro z ⟨u, hu, u', hu', rfl⟩ i
    have := hA.2 u hu u' hu' i
    rw [abs_le]
    constructor
    · have e : (1 - τ) / d * ‖u - u'‖ ^ 2 = 1 / d * ‖u - u'‖ ^ 2 - τ * (1 / d) * ‖u - u'‖ ^ 2 := by
        ring
      linarith [this.1]
    · have e : (1 + τ) / d * ‖u - u'‖ ^ 2 = 1 / d * ‖u - u'‖ ^ 2 + τ * (1 / d) * ‖u - u'‖ ^ 2 := by
        ring
      linarith [this.2]
  have hq : ∀ i, ‖A i (condMean S x xs i - mean x xs)‖ ^ 2 ≤
      (1 / d) * ‖condMean S x xs i - mean x xs‖ ^ 2 +
        3 * (τ * (1 / d)) * ((∑ v, |lam i v|) * ∑ v, |lam i v| * ‖y v‖ ^ 2) := by
    intro i
    rw [hu i]
    refine quad_bound (A i) (1 / d) τ (by positivity) y (lam i) (fun v => ?_) (fun v v' => ?_)
    · exact hbal _ ⟨x v, hx v, xs, hxs, rfl⟩ i
    · refine hbal _ ⟨x v, hx v, x v', hx v', ?_⟩ i
      simp [y]
  -- ∑ |λ_i| ≤ 2 and ∑_i |λ_i v| ≤ 2d/|Vtx|
  have hlam_abs : ∀ i v, |lam i v| ≤ n i v / cnt i + (Fintype.card Vtx : ℝ)⁻¹ := by
    intro i v
    have h0 : 0 ≤ n i v / cnt i := div_nonneg (Nat.cast_nonneg _) (hcpos i).le
    have h1 : 0 ≤ (Fintype.card Vtx : ℝ)⁻¹ := by positivity
    simp only [lam]; rw [abs_le]; constructor <;> linarith
  have hsum1 : ∀ i, ∑ v, |lam i v| ≤ 2 := by
    intro i
    calc ∑ v, |lam i v| ≤ ∑ v, (n i v / cnt i + (Fintype.card Vtx : ℝ)⁻¹) :=
          Finset.sum_le_sum fun v _ => hlam_abs i v
      _ = 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, hn_sum, div_self (hcpos i).ne',
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hV.ne']
        norm_num
  have hsum2 : ∀ v, ∑ i, |lam i v| ≤ 2 * d / Fintype.card Vtx := by
    intro v
    calc ∑ i, |lam i v| ≤ ∑ i, (n i v / cnt i + (Fintype.card Vtx : ℝ)⁻¹) :=
          Finset.sum_le_sum fun i _ => hlam_abs i v
      _ = 2 * d / Fintype.card Vtx := by
        simp_rw [hcnt]
        rw [Finset.sum_add_distrib, ← Finset.sum_div, hn_sum_i, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, hMdef]
        push_cast
        have hO : (0 : ℝ) < Fintype.card Occ := by exact_mod_cast Fintype.card_pos
        field_simp
        ring
  -- betweenVar = (1/d) ∑_i ‖a_i − a‖²
  have hB : betweenVar S x xs = (1 / d) * ∑ i, ‖condMean S x xs i - mean x xs‖ ^ 2 := by
    simp only [betweenVar]
    rw [sum_by_fib S (fun _ i => ‖condMean S x xs i - mean x xs‖ ^ 2)]
    simp_rw [Finset.sum_const, nsmul_eq_mul, card_fib]
    simp_rw [show ∀ i, (blockCount S i : ℝ) = cnt i from fun _ => rfl, hcnt, ← Finset.mul_sum,
      ← hMdef]
    field_simp
  -- assemble
  calc ∑ i, ‖A i (condMean S x xs i - mean x xs)‖ ^ 2
      ≤ ∑ i, ((1 / d) * ‖condMean S x xs i - mean x xs‖ ^ 2 +
          3 * (τ * (1 / d)) * ((∑ v, |lam i v|) * ∑ v, |lam i v| * ‖y v‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => hq i
    _ ≤ ∑ i, ((1 / d) * ‖condMean S x xs i - mean x xs‖ ^ 2 +
          3 * (τ * (1 / d)) * (2 * ∑ v, |lam i v| * ‖y v‖ ^ 2)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h0 : 0 ≤ ∑ v, |lam i v| * ‖y v‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
        have hk : 0 ≤ 3 * (τ * (1 / (d : ℝ))) := by positivity
        exact add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hsum1 i) h0) hk) _
    _ = betweenVar S x xs + 6 * τ * (1 / d) * ∑ v, (∑ i, |lam i v|) * ‖y v‖ ^ 2 := by
        rw [Finset.sum_add_distrib, hB, ← Finset.mul_sum]
        congr 1
        have : ∑ v, (∑ i, |lam i v|) * ‖y v‖ ^ 2 = ∑ i, ∑ v, |lam i v| * ‖y v‖ ^ 2 := by
          simp_rw [Finset.sum_mul]; exact Finset.sum_comm
        rw [this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ betweenVar S x xs + 6 * τ * (1 / d) * ∑ v, (2 * d / Fintype.card Vtx) * ‖y v‖ ^ 2 := by
        gcongr with v
        exact hsum2 v
    _ = betweenVar S x xs + 12 * τ * ((Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖x v - xs‖ ^ 2) := by
        rw [← Finset.mul_sum]
        field_simp
        simp only [y]; ring
