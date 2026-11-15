-- Prove2me | solution 1 for DetANN.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T07:50:07.134201+00:00
-- url     : https://prove2.me/submissions/7d45c474-d1df-4564-9074-465ff9b90d93

import Mathlib
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_TupleFamily
import Theorems.Thm_DetANN_walk_family_uniform

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

namespace DetANNSpecAux

open DetANN Matrix

variable {V : Type} [Fintype V] [DecidableEq V] {Δ : ℕ}

lemma adj_symm' (nbr : V → Fin Δ → V) (hund : IsUndirected nbr) (u v : V) :
    adjMatrix nbr u v = adjMatrix nbr v u := by
  simp [adjMatrix, hund u v]

lemma adj_rowsum' (nbr : V → Fin Δ → V) (hΔ : 1 ≤ Δ) (u : V) :
    ∑ v, adjMatrix nbr u v = 1 := by
  have hΔ' : (Δ : ℝ) ≠ 0 := by positivity
  have h : ∑ v, (edgeCount nbr u v : ℝ) = Δ := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin Δ)))
      (t := (Finset.univ : Finset V)) (f := nbr u) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this.symm
  simp only [adjMatrix, ← Finset.sum_div, h, div_self hΔ']

lemma pow_rowsum' (nbr : V → Fin Δ → V) (hΔ : 1 ≤ Δ) (ℓ : ℕ) (u : V) :
    ∑ v, (adjMatrix nbr ^ ℓ) u v = 1 := by
  induction ℓ generalizing u with
  | zero => simp [Matrix.one_apply]
  | succ ℓ ih =>
    rw [pow_succ']
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact adj_rowsum' nbr hΔ u

/-- `W` maps mean-zero vectors to mean-zero vectors (column sums are `1` by symmetry). -/
lemma mulVec_sum_zero (nbr : V → Fin Δ → V) (hΔ : 1 ≤ Δ) (hund : IsUndirected nbr)
    (f : V → ℝ) (hf : ∑ v, f v = 0) : ∑ u, (adjMatrix nbr *ᵥ f) u = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  have : ∀ v, ∑ u, adjMatrix nbr u v * f v = f v := by
    intro v
    rw [← Finset.sum_mul]
    simp_rw [adj_symm' nbr hund _ v]
    rw [adj_rowsum' nbr hΔ v, one_mul]
  simp_rw [this]; exact hf

/-- Iterating the contraction: `‖W^j f‖² ≤ (θ^j)² ‖f‖²` for mean-zero `f`. -/
lemma iterate_contract (nbr : V → Fin Δ → V) (hΔ : 1 ≤ Δ) (hund : IsUndirected nbr)
    (θ : ℝ) (hW : ContractsMeanZero (adjMatrix nbr) θ) (j : ℕ) (f : V → ℝ)
    (hf : ∑ v, f v = 0) :
    ∑ u, ((adjMatrix nbr ^ j) *ᵥ f) u ^ 2 ≤ (θ ^ j) ^ 2 * ∑ v, f v ^ 2 ∧
      ∑ u, ((adjMatrix nbr ^ j) *ᵥ f) u = 0 := by
  induction j with
  | zero => simp [hf]
  | succ j ih =>
    have e : (adjMatrix nbr ^ (j + 1)) *ᵥ f = adjMatrix nbr *ᵥ ((adjMatrix nbr ^ j) *ᵥ f) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [e]
    refine ⟨?_, mulVec_sum_zero nbr hΔ hund _ ih.2⟩
    calc ∑ u, (adjMatrix nbr *ᵥ ((adjMatrix nbr ^ j) *ᵥ f)) u ^ 2
        ≤ θ ^ 2 * ∑ u, ((adjMatrix nbr ^ j) *ᵥ f) u ^ 2 := hW _ ih.2
      _ ≤ θ ^ 2 * ((θ ^ j) ^ 2 * ∑ v, f v ^ 2) :=
          mul_le_mul_of_nonneg_left ih.1 (sq_nonneg _)
      _ = (θ ^ (j + 1)) ^ 2 * ∑ v, f v ^ 2 := by ring

end DetANNSpecAux

open DetANN DetANNFinAux DetANNSpecAux Matrix in
theorem solution {d Δ : ℕ} (nbr : Fin d → Fin Δ → Fin d) (hΔ : 1 ≤ Δ)
    (hund : IsUndirected nbr) (θ₀ : ℝ) (hθ0 : 0 ≤ θ₀) (hθ1 : θ₀ < 1)
    (hW : ContractsMeanZero (adjMatrix nbr) θ₀) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (x : Fin d → EuclideanSpace ℝ (Fin d)) (xs : EuclideanSpace ℝ (Fin d)) :
    betweenVar (walkEnd nbr ℓ) x xs ≤
      (θ₀ ^ ℓ) ^ 2 / (1 - (θ₀ ^ ℓ) ^ 2) * withinVar (walkEnd nbr ℓ) x xs := by
  -- the case d = 0 is empty
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    simp [betweenVar, withinVar]
  have : Nonempty (Fin d) := ⟨⟨0, hdpos⟩⟩
  have : Nonempty (Fin ℓ → Fin Δ) := ⟨fun _ => ⟨0, hΔ⟩⟩
  obtain ⟨hcount, hprob⟩ := walk_family_uniform nbr hΔ hund ℓ
  set S := walkEnd nbr ℓ with hSdef
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hΔR : (0 : ℝ) < (Δ : ℝ) ^ ℓ := pow_pos (by exact_mod_cast hΔ) ℓ
  have hcardO : (Fintype.card (Fin ℓ → Fin Δ) : ℝ) = (Δ : ℝ) ^ ℓ := by simp
  have hcardV : (Fintype.card (Fin d) : ℝ) = d := by simp
  have hS : UniformFreq S := by
    intro i
    rw [hcount i, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, mul_comm]
  set M : ℝ := ((Fintype.card (Fin d) * Fintype.card (Fin ℓ → Fin Δ) : ℕ) : ℝ) with hMdef
  have hM : 0 < M := M_pos
  have hMval : M = d * (Δ : ℝ) ^ ℓ := by rw [hMdef]; push_cast; rw [hcardV, hcardO]
  set y : Fin d → EuclideanSpace ℝ (Fin d) := fun v => x v - xs
  set a := mean x xs
  set ai := condMean S x xs
  set K := adjMatrix nbr ^ ℓ
  set 𝒱 := withinVar S x xs
  set B := betweenVar S x xs
  set ρ := θ₀ ^ ℓ
  -- (1) the conditional means are W^ℓ-averages: a_i = ∑_v K_{iv} y_v
  have hai : ∀ i, ai i = ∑ v, K i v • y v := by
    intro i
    have h1 : ai i = ((Δ : ℝ) ^ ℓ)⁻¹ • ∑ p ∈ fib S i, y p.1 := by
      simp only [ai, condMean_eq, card_fib, hcount i]; push_cast; rfl
    rw [h1, Finset.sum_filter, Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const]
    rw [← hprob i v, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, div_eq_inv_mul]
  have hK1 : ∀ i, ∑ v, K i v = 1 := fun i => pow_rowsum' nbr hΔ ℓ i
  have haia : ∀ i, ai i - a = ∑ v, K i v • (y v - a) := by
    intro i
    rw [hai i]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hK1, one_smul]
  have hzsum : ∑ v, (y v - a) = 0 := by
    have ha : a = (d : ℝ)⁻¹ • ∑ v, y v := by simp only [a, mean, hcardV]; rfl
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ha,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hdR.ne', one_smul, sub_self]
  -- (2) between-block variance B = (1/d) ∑_i ‖a_i − a‖²
  have hB : B = (1 / d) * ∑ i, ‖ai i - a‖ ^ 2 := by
    simp only [B, betweenVar]
    rw [sum_by_fib S (fun _ i => ‖condMean S x xs i - mean x xs‖ ^ 2)]
    simp_rw [Finset.sum_const, nsmul_eq_mul, card_fib, hcount]
    rw [← Finset.mul_sum, ← hMdef, hMval]
    push_cast
    field_simp
    rfl
  -- (3) total variance: (1/d) ∑_v ‖y_v − a‖² = 𝒱 + B
  have htot : (1 / (d : ℝ)) * ∑ v, ‖y v - a‖ ^ 2 = 𝒱 + B := by
    have hpairs : ∑ p : Fin d × (Fin ℓ → Fin Δ), ‖y p.1 - a‖ ^ 2 =
        Fintype.card (Fin ℓ → Fin Δ) * ∑ v, ‖y v - a‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]; simp
    have hfib : ∑ p : Fin d × (Fin ℓ → Fin Δ), ‖y p.1 - a‖ ^ 2 =
        ∑ p : Fin d × (Fin ℓ → Fin Δ), ‖ai (S p.1 p.2) - a‖ ^ 2 +
          ∑ p : Fin d × (Fin ℓ → Fin Δ), ‖x p.1 - xs - ai (S p.1 p.2)‖ ^ 2 := by
      rw [sum_by_fib S (fun p _ => ‖y p.1 - a‖ ^ 2), sum_by_fib S (fun _ i => ‖ai i - a‖ ^ 2),
        sum_by_fib S (fun p i => ‖x p.1 - xs - ai i‖ ^ 2), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := sum_sq_dev (fib S i) (fun p => y p.1) a
      have hm : ((fib S i).card : ℝ)⁻¹ • ∑ p ∈ fib S i, y p.1 = ai i := by
        simp [ai, condMean_eq, y]
      rw [hm] at h
      simp_rw [norm_sub_rev (y _) a, h, norm_sub_rev a (ai i), Finset.sum_const, nsmul_eq_mul]
      rfl
    have h𝒱 : 𝒱 = M⁻¹ * ∑ p : Fin d × (Fin ℓ → Fin Δ), ‖x p.1 - xs - ai (S p.1 p.2)‖ ^ 2 := rfl
    have hB' : B = M⁻¹ * ∑ p : Fin d × (Fin ℓ → Fin Δ), ‖ai (S p.1 p.2) - a‖ ^ 2 := rfl
    rw [h𝒱, hB', add_comm (M⁻¹ * _) (M⁻¹ * _), ← mul_add, ← hfib, hpairs, hMval, hcardO]
    field_simp
  -- (4) the spectral bound, coordinatewise: ∑_i ‖a_i − a‖² ≤ ρ² ∑_v ‖y_v − a‖²
  have hspec : ∑ i, ‖ai i - a‖ ^ 2 ≤ ρ ^ 2 * ∑ v, ‖y v - a‖ ^ 2 := by
    simp_rw [haia, EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun v c => (y v - a) c ^ 2), Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    set f : Fin d → ℝ := fun v => (y v - a) c
    have hf : ∑ v, f v = 0 := by
      simp only [f]
      have := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z c) hzsum
      simpa [WithLp.ofLp_sum] using this
    have key := (iterate_contract nbr hΔ hund θ₀ hW ℓ f hf).1
    have e : ∀ i, (∑ v, K i v • (y v - a)) c = (K *ᵥ f) i := by
      intro i
      simp [Matrix.mulVec, dotProduct, f, WithLp.ofLp_sum]
    simp_rw [e]
    exact key
  -- (5) combine: B ≤ ρ²(𝒱 + B), so (1 − ρ²) B ≤ ρ² 𝒱
  have hρ0 : 0 ≤ ρ := pow_nonneg hθ0 ℓ
  have hρ1 : ρ < 1 := pow_lt_one₀ hθ0 hθ1 (by omega)
  have h1ρ : 0 < 1 - ρ ^ 2 := by nlinarith
  have hBle : B ≤ ρ ^ 2 * (𝒱 + B) := by
    rw [← htot, hB]
    have := mul_le_mul_of_nonneg_left hspec (show (0 : ℝ) ≤ 1 / d by positivity)
    linarith [show 1 / (d : ℝ) * (ρ ^ 2 * ∑ v, ‖y v - a‖ ^ 2) =
      ρ ^ 2 * (1 / d * ∑ v, ‖y v - a‖ ^ 2) by ring]
  rw [div_mul_eq_mul_div, le_div_iff₀ h1ρ]
  nlinarith
