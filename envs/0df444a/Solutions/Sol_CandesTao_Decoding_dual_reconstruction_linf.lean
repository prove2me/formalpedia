-- Prove2me | solution 1 for CandesTao.Decoding.dual_reconstruction_linf
-- status  : ACCEPTED   (prove)
-- author  : @radokirov
-- created : 2026-10-04T00:56:55.526232+00:00
-- url     : https://prove2.me/submissions/79a832d6-d47f-4187-88ce-150273ed92a4

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_CandesTao_Decoding_L1Minimization
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic

open CandesTao.Decoding

namespace CandesTaoLem22

lemma nsq {n : ℕ} (x : Fin n → ℝ) : l2Norm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]

lemma l2_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ l2Norm x := Real.sqrt_nonneg _

lemma eq_zero_of_l2 {n : ℕ} (x : Fin n → ℝ) (h : l2Norm x = 0) : x = 0 := by
  have h2 : ∑ i, x i ^ 2 = 0 := by rw [← nsq, h]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))] at h2
  funext i
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h2 i (Finset.mem_univ i))

lemma dot_self_eq {n : ℕ} (x : Fin n → ℝ) : dotProduct x x = l2Norm x ^ 2 := by
  rw [nsq, dotProduct]; exact Finset.sum_congr rfl fun i _ => by ring

/-- Cauchy–Schwarz for `l2Norm`. -/
lemma abs_dot_le {n : ℕ} (x y : Fin n → ℝ) : |dotProduct x y| ≤ l2Norm x * l2Norm y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have h2 : dotProduct x y ^ 2 ≤ (l2Norm x * l2Norm y) ^ 2 := by
    rw [mul_pow, nsq, nsq]; exact h
  exact abs_le_of_sq_le_sq' h2 (mul_nonneg (l2_nonneg _) (l2_nonneg _)) |> abs_le.mpr

lemma mulVec_sq_le {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (x : Fin m → ℝ) :
    l2Norm (F.mulVec x) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * l2Norm x ^ 2 := by
  rw [nsq, nsq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

def DS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : Set ℝ :=
  {δ : ℝ | 0 ≤ δ ∧ ∀ T : Finset (Fin m), T.card ≤ k → ∀ c : Fin m → ℝ, SupportedOn c T →
    (1 - δ) * l2Norm c ^ 2 ≤ l2Norm (F.mulVec c) ^ 2 ∧
    l2Norm (F.mulVec c) ^ 2 ≤ (1 + δ) * l2Norm c ^ 2}

def TS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k k' : ℕ) : Set ℝ :=
  {θ : ℝ | 0 ≤ θ ∧ ∀ T T' : Finset (Fin m), Disjoint T T' → T.card ≤ k → T'.card ≤ k' →
    ∀ c c' : Fin m → ℝ, SupportedOn c T → SupportedOn c' T' →
    |dotProduct (F.mulVec c) (F.mulVec c')| ≤ θ * l2Norm c * l2Norm c'}

lemma DS_nonempty {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : (DS F k).Nonempty := by
  refine ⟨max 1 (∑ i, ∑ j, F i j ^ 2), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro U _ x _
  have h0 : 0 ≤ l2Norm x ^ 2 := sq_nonneg _
  have h1 : 0 ≤ l2Norm (F.mulVec x) ^ 2 := sq_nonneg _
  have hb := mulVec_sq_le F x
  have hm1 : 1 ≤ max 1 (∑ i, ∑ j, F i j ^ 2) := le_max_left _ _
  have hmK : (∑ i, ∑ j, F i j ^ 2) ≤ max 1 (∑ i, ∑ j, F i j ^ 2) := le_max_right _ _
  constructor
  · nlinarith
  · nlinarith

lemma norm_mulVec_le {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (x : Fin m → ℝ) :
    l2Norm (F.mulVec x) ≤ Real.sqrt (∑ i, ∑ j, F i j ^ 2) * l2Norm x := by
  have hK : 0 ≤ ∑ i, ∑ j, F i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← Real.sqrt_sq (l2_nonneg (F.mulVec x)), ← Real.sqrt_sq (l2_nonneg x),
    ← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt (mulVec_sq_le F x)

lemma TS_nonempty {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k k' : ℕ) :
    (TS F k k').Nonempty := by
  set K := ∑ i, ∑ j, F i j ^ 2 with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine ⟨K, hK, ?_⟩
  intro T T' _ _ _ c c' _ _
  have e1 := norm_mulVec_le F c
  have e2 := norm_mulVec_le F c'
  have hs : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK
  calc |dotProduct (F.mulVec c) (F.mulVec c')|
      ≤ l2Norm (F.mulVec c) * l2Norm (F.mulVec c') := abs_dot_le _ _
    _ ≤ (Real.sqrt K * l2Norm c) * (Real.sqrt K * l2Norm c') :=
        mul_le_mul e1 e2 (l2_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (l2_nonneg _))
    _ = (Real.sqrt K * Real.sqrt K) * l2Norm c * l2Norm c' := by ring
    _ = K * l2Norm c * l2Norm c' := by rw [hs]

/-- The infimum `θ_{S,S'}` itself satisfies the orthogonality inequality. -/
lemma orth_bound {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ)
    (T T' : Finset (Fin m)) (hTT : Disjoint T T') (hT : T.card ≤ S) (hT' : T'.card ≤ S')
    (x y : Fin m → ℝ) (hx : SupportedOn x T) (hy : SupportedOn y T') :
    |dotProduct (F.mulVec x) (F.mulVec y)| ≤
      restrictedOrthogonalityConst F S S' * l2Norm x * l2Norm y := by
  have e : restrictedOrthogonalityConst F S S' = sInf (TS F S S') := rfl
  rw [e]
  by_cases h0 : l2Norm x * l2Norm y = 0
  · rcases mul_eq_zero.mp h0 with h | h
    · rw [eq_zero_of_l2 x h, Matrix.mulVec_zero, zero_dotProduct, abs_zero]
      unfold l2Norm; simp
    · rw [eq_zero_of_l2 y h, Matrix.mulVec_zero, dotProduct_zero, abs_zero]
      unfold l2Norm; simp
  have hpos : 0 < l2Norm x * l2Norm y :=
    lt_of_le_of_ne (mul_nonneg (l2_nonneg _) (l2_nonneg _)) (Ne.symm h0)
  have : |dotProduct (F.mulVec x) (F.mulVec y)| / (l2Norm x * l2Norm y) ≤ sInf (TS F S S') := by
    apply le_csInf (TS_nonempty F S S')
    intro θ hθ
    rw [div_le_iff₀ hpos]
    have := hθ.2 T T' hTT hT hT' x y hx hy
    linarith [this, show θ * l2Norm x * l2Norm y = θ * (l2Norm x * l2Norm y) by ring]
  rw [div_le_iff₀ hpos] at this
  linarith [this, show sInf (TS F S S') * l2Norm x * l2Norm y =
    sInf (TS F S S') * (l2Norm x * l2Norm y) by ring]

/-- The infimum `δ_S` itself satisfies the two isometry inequalities. -/
lemma iso_bounds {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ) (T : Finset (Fin m))
    (hT : T.card ≤ S) (x : Fin m → ℝ) (hx : SupportedOn x T) :
    (1 - restrictedIsometryConst F S) * l2Norm x ^ 2 ≤ l2Norm (F.mulVec x) ^ 2 ∧
    l2Norm (F.mulVec x) ^ 2 ≤ (1 + restrictedIsometryConst F S) * l2Norm x ^ 2 := by
  have e : restrictedIsometryConst F S = sInf (DS F S) := rfl
  rw [e]
  by_cases h0 : l2Norm x = 0
  · rw [h0, eq_zero_of_l2 x h0, Matrix.mulVec_zero]
    have : l2Norm (0 : Fin p → ℝ) = 0 := by unfold l2Norm; simp
    rw [this]; simp
  have hpos : 0 < l2Norm x ^ 2 := by positivity
  set q := l2Norm (F.mulVec x) ^ 2 / l2Norm x ^ 2 with hq
  have hqx : q * l2Norm x ^ 2 = l2Norm (F.mulVec x) ^ 2 := by
    rw [hq]; field_simp
  constructor
  · have : 1 - q ≤ sInf (DS F S) := by
      apply le_csInf (DS_nonempty F S)
      intro δ hδ
      have h := (hδ.2 T hT x hx).1
      rw [← hqx] at h
      nlinarith
    nlinarith
  · have : q - 1 ≤ sInf (DS F S) := by
      apply le_csInf (DS_nonempty F S)
      intro δ hδ
      have h := (hδ.2 T hT x hx).2
      rw [← hqx] at h
      nlinarith
    nlinarith

end CandesTaoLem22

namespace CandesTaoLem22

lemma sum_dot_column {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (w : Fin p → ℝ)
    (h : Fin m → ℝ) :
    ∑ j, h j * dotProduct w (column F j) = dotProduct w (F.mulVec h) := by
  simp only [dotProduct, column, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma dot_column_eq {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (w : Fin p → ℝ) (j : Fin m) :
    dotProduct w (column F j) = (F.transpose.mulVec w) j := by
  simp only [dotProduct, column, Matrix.mulVec, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dot_FF {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (u : Fin m → ℝ) :
    dotProduct u (F.transpose.mulVec (F.mulVec u)) = l2Norm (F.mulVec u) ^ 2 := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dot_self_eq]

end CandesTaoLem22


namespace CandesTaoLem22

/-- restriction of `x` to `A` -/
noncomputable def rs {m : ℕ} (A : Finset (Fin m)) (x : Fin m → ℝ) : Fin m → ℝ :=
  fun j => if j ∈ A then x j else 0

lemma rs_supp {m : ℕ} (A : Finset (Fin m)) (x : Fin m → ℝ) : SupportedOn (rs A x) A := by
  intro j hj; simp [rs, hj]

lemma rs_nsq {m : ℕ} (A : Finset (Fin m)) (x : Fin m → ℝ) :
    l2Norm (rs A x) ^ 2 = ∑ j ∈ A, x j ^ 2 := by
  rw [nsq]
  have : ∀ j, rs A x j ^ 2 = if j ∈ A then x j ^ 2 else 0 := by
    intro j; unfold rs; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma rs_union {m : ℕ} (A B : Finset (Fin m)) (hAB : Disjoint A B) (x : Fin m → ℝ) :
    rs (A ∪ B) x = rs A x + rs B x := by
  funext j
  simp only [rs, Pi.add_apply, Finset.mem_union]
  by_cases hA : j ∈ A
  · have hB : j ∉ B := Finset.disjoint_left.mp hAB hA
    simp [hA, hB]
  · simp [hA]

/-- `‖x_A‖ ≤ √S τ` when `|A| ≤ S` and the entries are bounded by `τ`. -/
lemma rs_l2_le {m : ℕ} (A : Finset (Fin m)) (x : Fin m → ℝ) (S : ℕ) (hA : A.card ≤ S)
    (τ : ℝ) (hτ : 0 ≤ τ) (hx : ∀ j ∈ A, |x j| ≤ τ) :
    l2Norm (rs A x) ≤ Real.sqrt S * τ := by
  rw [← Real.sqrt_sq (l2_nonneg _), rs_nsq, ← Real.sqrt_sq hτ, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  calc ∑ j ∈ A, x j ^ 2 ≤ ∑ j ∈ A, τ ^ 2 := by
        apply Finset.sum_le_sum; intro j hj
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx j hj) 2
    _ = A.card * τ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ S * τ ^ 2 := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hA) (sq_nonneg _)

/-- Cauchy–Schwarz: `∑_A |x_j| ≤ √S ‖x_A‖` when `|A| ≤ S`. -/
lemma l1_le_sqrt_l2 {m : ℕ} (A : Finset (Fin m)) (x : Fin m → ℝ) (S : ℕ) (hA : A.card ≤ S) :
    ∑ j ∈ A, |x j| ≤ Real.sqrt S * l2Norm (rs A x) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq A (fun j => |x j|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, sq_abs] at hcs
  have h0 : 0 ≤ ∑ j ∈ A, |x j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h2 : (∑ j ∈ A, |x j|) ^ 2 ≤ (Real.sqrt S * l2Norm (rs A x)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), rs_nsq]
    calc (∑ j ∈ A, |x j|) ^ 2 ≤ (∑ j ∈ A, x j ^ 2) * A.card := hcs
      _ ≤ (∑ j ∈ A, x j ^ 2) * S := by
          apply mul_le_mul_of_nonneg_left (by exact_mod_cast hA)
            (Finset.sum_nonneg fun j _ => sq_nonneg _)
      _ = S * ∑ j ∈ A, x j ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ h0 (mul_nonneg (Real.sqrt_nonneg _) (l2_nonneg _))
    (by norm_num)).mp h2

/-- A "top-`k`" subset: every entry outside it is at most every entry inside it. -/
lemma exists_top {m : ℕ} (R : Finset (Fin m)) (x : Fin m → ℝ) (k : ℕ) (hk : k ≤ R.card) :
    ∃ B ⊆ R, B.card = k ∧ ∀ j ∈ B, ∀ i ∈ R \ B, |x i| ≤ |x j| := by
  classical
  obtain ⟨B, hB, hmax⟩ := (R.powersetCard k).exists_max_image
    (fun B => ∑ j ∈ B, |x j|) (Finset.powersetCard_nonempty.mpr hk)
  rw [Finset.mem_powersetCard] at hB
  refine ⟨B, hB.1, hB.2, ?_⟩
  intro j hj i hi
  by_contra hlt
  push Not at hlt
  rw [Finset.mem_sdiff] at hi
  set B' := insert i (B.erase j) with hB'
  have hiB : i ∉ B.erase j := fun h => hi.2 (Finset.mem_of_mem_erase h)
  have hB'mem : B' ∈ R.powersetCard k := by
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro t ht
      rw [hB', Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · exact hi.1
      · exact hB.1 (Finset.mem_of_mem_erase ht)
    · rw [hB', Finset.card_insert_of_notMem hiB, Finset.card_erase_of_mem hj, hB.2]
      have : 1 ≤ k := by rw [← hB.2]; exact Finset.card_pos.mpr ⟨j, hj⟩
      omega
  have hsum : ∑ t ∈ B', |x t| = |x i| + (∑ t ∈ B, |x t| - |x j|) := by
    rw [hB', Finset.sum_insert hiB, ← Finset.add_sum_erase B _ hj]
    ring
  have := hmax B' hB'mem
  rw [hsum] at this
  linarith

/-- entries outside a top-`k` set are at most the average over it -/
lemma le_avg {m : ℕ} (R B : Finset (Fin m)) (x : Fin m → ℝ) (k : ℕ) (hk : 0 < k)
    (hB : B.card = k) (htop : ∀ j ∈ B, ∀ i ∈ R \ B, |x i| ≤ |x j|) :
    ∀ i ∈ R \ B, |x i| ≤ (∑ j ∈ B, |x j|) / k := by
  intro i hi
  rw [le_div_iff₀ (by exact_mod_cast hk)]
  have : ∑ j ∈ B, |x i| ≤ ∑ j ∈ B, |x j| := Finset.sum_le_sum fun j hj => htop j hj i hi
  rw [Finset.sum_const, hB, nsmul_eq_mul] at this
  linarith

end CandesTaoLem22

namespace CandesTaoLem22

/-- Block decomposition: the tail `x_R` (entries `≤ τ`) interacts with a `2S`-sparse `y` at most
like `θ_{S,2S} (√S τ + ‖x_R‖₁/√S) ‖y‖`. Proved by peeling off top-`S` blocks. -/
lemma block_bound {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ) (hS : 1 ≤ S) :
    ∀ n : ℕ, ∀ (R Y : Finset (Fin m)) (x y : Fin m → ℝ) (τ : ℝ),
      R.card ≤ n → Disjoint R Y → Y.card ≤ S' → SupportedOn y Y → 0 ≤ τ →
      (∀ i ∈ R, |x i| ≤ τ) →
      |dotProduct (F.mulVec (rs R x)) (F.mulVec y)| ≤
        restrictedOrthogonalityConst F S S' *
          (Real.sqrt S * τ + (∑ i ∈ R, |x i|) / Real.sqrt S) * l2Norm y := by
  classical
  have hθ0 : 0 ≤ restrictedOrthogonalityConst F S S' :=
    Real.sInf_nonneg fun x hx => hx.1
  have hsq : 0 < Real.sqrt (S : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hS)
  -- the case of a single block
  have small : ∀ (R Y : Finset (Fin m)) (x y : Fin m → ℝ) (τ : ℝ),
      R.card ≤ S → Disjoint R Y → Y.card ≤ S' → SupportedOn y Y → 0 ≤ τ →
      (∀ i ∈ R, |x i| ≤ τ) →
      |dotProduct (F.mulVec (rs R x)) (F.mulVec y)| ≤
        restrictedOrthogonalityConst F S S' * (Real.sqrt S * τ) * l2Norm y := by
    intro R Y x y τ hR hRY hY hy hτ hx
    have h1 := orth_bound F S S' R Y hRY hR hY (rs R x) y (rs_supp R x) hy
    have h2 := rs_l2_le R x S hR τ hτ hx
    calc _ ≤ _ := h1
      _ ≤ restrictedOrthogonalityConst F S S' * (Real.sqrt S * τ) * l2Norm y := by
          apply mul_le_mul_of_nonneg_right _ (l2_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 hθ0
  have hsum0 : ∀ R : Finset (Fin m), ∀ x : Fin m → ℝ, 0 ≤ (∑ i ∈ R, |x i|) / Real.sqrt S :=
    fun R x => div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) hsq.le
  intro n
  induction n with
  | zero =>
    intro R Y x y τ hR hRY hY hy hτ hx
    have hRe : R = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hRe
    have : rs (∅ : Finset (Fin m)) x = 0 := by funext j; simp [rs]
    rw [this, Matrix.mulVec_zero, zero_dotProduct, abs_zero]
    exact mul_nonneg (mul_nonneg hθ0 (by positivity)) (l2_nonneg _)
  | succ n ih =>
    intro R Y x y τ hR hRY hY hy hτ hx
    by_cases hRS : R.card ≤ S
    · have := small R Y x y τ hRS hRY hY hy hτ hx
      calc _ ≤ _ := this
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (l2_nonneg _)
          apply mul_le_mul_of_nonneg_left _ hθ0
          linarith [hsum0 R x]
    push Not at hRS
    obtain ⟨B, hBR, hBc, htop⟩ := exists_top R x S hRS.le
    set R' := R \ B with hR'
    have hR'c : R'.card ≤ n := by
      have h := Finset.card_sdiff_add_card_eq_card hBR
      show (R \ B).card ≤ n
      omega
    have hsplit : rs R x = rs B x + rs R' x := by
      rw [← rs_union B R' Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hBR]
    set τ' := (∑ j ∈ B, |x j|) / S with hτ'
    have hτ'0 : 0 ≤ τ' := div_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (by positivity)
    have hxB : ∀ i ∈ B, |x i| ≤ τ := fun i hi => hx i (hBR hi)
    have hxR' : ∀ i ∈ R', |x i| ≤ τ' := le_avg R B x S (by omega) hBc htop
    have e1 := small B Y x y τ hBc.le (Finset.disjoint_of_subset_left hBR hRY) hY hy hτ hxB
    have e2 := ih R' Y x y τ' hR'c (Finset.disjoint_of_subset_left Finset.sdiff_subset hRY)
      hY hy hτ'0 hxR'
    have hτ'eq : Real.sqrt S * τ' = (∑ j ∈ B, |x j|) / Real.sqrt S := by
      rw [hτ', eq_div_iff hsq.ne']
      have hss : Real.sqrt (S : ℝ) * Real.sqrt S = S := Real.mul_self_sqrt (by positivity)
      have hS0 : (S : ℝ) ≠ 0 := by positivity
      calc Real.sqrt S * ((∑ j ∈ B, |x j|) / S) * Real.sqrt S
          = (∑ j ∈ B, |x j|) * (Real.sqrt S * Real.sqrt S) / S := by ring
        _ = ∑ j ∈ B, |x j| := by rw [hss]; field_simp
    have hsumR : ∑ i ∈ R, |x i| = ∑ j ∈ B, |x j| + ∑ i ∈ R', |x i| := by
      rw [← Finset.sum_sdiff hBR]; ring
    rw [hsplit, Matrix.mulVec_add, add_dotProduct]
    calc _ ≤ |dotProduct (F.mulVec (rs B x)) (F.mulVec y)| +
            |dotProduct (F.mulVec (rs R' x)) (F.mulVec y)| := abs_add_le _ _
      _ ≤ restrictedOrthogonalityConst F S S' * (Real.sqrt S * τ) * l2Norm y +
          restrictedOrthogonalityConst F S S' *
            (Real.sqrt S * τ' + (∑ i ∈ R', |x i|) / Real.sqrt S) * l2Norm y := add_le_add e1 e2
      _ = restrictedOrthogonalityConst F S S' *
            (Real.sqrt S * τ + (∑ i ∈ R, |x i|) / Real.sqrt S) * l2Norm y := by
          rw [hτ'eq, hsumR]; ring

end CandesTaoLem22

namespace CandesTaoLem22

lemma nsq_add {n : ℕ} (x y : Fin n → ℝ) :
    l2Norm (x + y) ^ 2 = l2Norm x ^ 2 + 2 * dotProduct x y + l2Norm y ^ 2 := by
  rw [nsq, nsq, nsq, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

lemma sqrt_mul_div {S : ℕ} (hS : 1 ≤ S) (X : ℝ) :
    Real.sqrt S * (X / S) = X / Real.sqrt S := by
  have hsq : 0 < Real.sqrt (S : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hS)
  rw [eq_div_iff hsq.ne']
  have hss : Real.sqrt (S : ℝ) * Real.sqrt S = S := Real.mul_self_sqrt (by positivity)
  have hS0 : (S : ℝ) ≠ 0 := by positivity
  calc Real.sqrt S * (X / S) * Real.sqrt S = X * (Real.sqrt S * Real.sqrt S) / S := by ring
    _ = X := by rw [hss]; field_simp

end CandesTaoLem22


namespace CandesTaoLem22

/-- Null-space inequality: for `φ ∈ ker F`,
`(1 - δ_S - θ_{S,S}) ‖φ_T‖ ≤ θ_{S,S} ‖φ_{Tᶜ}‖₁ / √S`. -/
lemma nsp {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ) (hS : 1 ≤ S)
    (T : Finset (Fin m)) (hT : T.card ≤ S) (φ : Fin m → ℝ) (hφ : F.mulVec φ = 0)
    (hgap : 0 < 1 - restrictedIsometryConst F S - restrictedOrthogonalityConst F S S) :
    (1 - restrictedIsometryConst F S - restrictedOrthogonalityConst F S S) * l2Norm (rs T φ) ≤
      restrictedOrthogonalityConst F S S * ((∑ j ∈ Tᶜ, |φ j|) / Real.sqrt S) := by
  classical
  set δ := restrictedIsometryConst F S with hδdef
  set θ := restrictedOrthogonalityConst F S S with hθdef
  have hθ0 : 0 ≤ θ := Real.sInf_nonneg fun x hx => hx.1
  have hsq : 0 < Real.sqrt (S : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hS)
  set O := Tᶜ with hO
  obtain ⟨T₁, hT₁O, hT₁c, htop⟩ := exists_top O φ (min S O.card) (min_le_right _ _)
  set R := O \ T₁ with hR
  have hTT₁ : Disjoint T T₁ := by
    rw [Finset.disjoint_left]; intro j hjT hjT₁
    have := hT₁O hjT₁; rw [hO, Finset.mem_compl] at this; exact this hjT
  have hT₁S : T₁.card ≤ S := by rw [hT₁c]; exact min_le_left _ _
  have hRT : Disjoint R T := by
    rw [Finset.disjoint_left]; intro j hjR hjT
    rw [hR, Finset.mem_sdiff, hO, Finset.mem_compl] at hjR; exact hjR.1 hjT
  have hRT₁ : Disjoint R T₁ := by
    rw [Finset.disjoint_left]; intro j hjR hjT₁
    rw [hR, Finset.mem_sdiff] at hjR; exact hjR.2 hjT₁
  set τ := (∑ j ∈ T₁, |φ j|) / S with hτ
  have hτ0 : 0 ≤ τ := div_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (by positivity)
  have hxR : ∀ i ∈ R, |φ i| ≤ τ := by
    intro i hi
    have hk : min S O.card = S := by
      have hlt : T₁.card < O.card := by
        apply Finset.card_lt_card
        refine ⟨hT₁O, fun hsub => ?_⟩
        rw [hR, Finset.mem_sdiff] at hi
        exact hi.2 (hsub hi.1)
      rw [hT₁c] at hlt
      omega
    exact le_avg O T₁ φ S (by omega) (hT₁c.trans hk) htop i hi
  set L := ∑ j ∈ O, |φ j| with hL
  have hLsplit : L = ∑ j ∈ T₁, |φ j| + ∑ i ∈ R, |φ i| := by
    rw [hL, hR, ← Finset.sum_sdiff hT₁O]; ring
  set Λ := θ * (L / Real.sqrt S) with hΛ
  have hΛ0 : 0 ≤ Λ :=
    mul_nonneg hθ0 (div_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) hsq.le)
  set y := rs T φ with hydef
  set z := rs T₁ φ with hzdef
  set r := rs R φ with hrdef
  have hdecomp : φ = y + z + r := by
    funext j
    simp only [hydef, hzdef, hrdef, rs, Pi.add_apply, hR, Finset.mem_sdiff, hO,
      Finset.mem_compl]
    by_cases hjT : j ∈ T
    · have : j ∉ T₁ := Finset.disjoint_left.mp hTT₁ hjT
      simp [hjT, this]
    · by_cases hjT₁ : j ∈ T₁
      · simp [hjT, hjT₁]
      · simp [hjT, hjT₁]
  have hF : F.mulVec y + F.mulVec z + F.mulVec r = 0 := by
    rw [← Matrix.mulVec_add, ← Matrix.mulVec_add, ← hdecomp, hφ]
  -- block bounds against `y` and `z`
  have bY := block_bound F S S hS R.card R T φ y τ le_rfl hRT hT (rs_supp T φ) hτ0 hxR
  have bZ := block_bound F S S hS R.card R T₁ φ z τ le_rfl hRT₁ hT₁S (rs_supp T₁ φ) hτ0 hxR
  rw [← hθdef, hτ, sqrt_mul_div hS, ← add_div, ← hLsplit] at bY bZ
  set a := l2Norm y
  set b := l2Norm z
  have ha0 : 0 ≤ a := l2_nonneg _
  have hb0 : 0 ≤ b := l2_nonneg _
  have oYZ := orth_bound F S S T T₁ hTT₁ hT hT₁S y z (rs_supp T φ) (rs_supp T₁ φ)
  have oZY := orth_bound F S S T₁ T hTT₁.symm hT₁S hT z y (rs_supp T₁ φ) (rs_supp T φ)
  rw [← hθdef] at oYZ oZY
  have iY := (iso_bounds F S T hT y (rs_supp T φ)).1
  have iZ := (iso_bounds F S T₁ hT₁S z (rs_supp T₁ φ)).1
  rw [← hδdef] at iY iZ
  have h0y : dotProduct (F.mulVec y) (F.mulVec y + F.mulVec z + F.mulVec r) = 0 := by
    rw [hF, dotProduct_zero]
  have h0z : dotProduct (F.mulVec z) (F.mulVec y + F.mulVec z + F.mulVec r) = 0 := by
    rw [hF, dotProduct_zero]
  rw [dotProduct_add, dotProduct_add] at h0y h0z
  have cY1 := neg_le_abs (dotProduct (F.mulVec y) (F.mulVec z))
  have cY2 := neg_le_abs (dotProduct (F.mulVec r) (F.mulVec y))
  have cZ1 := neg_le_abs (dotProduct (F.mulVec z) (F.mulVec y))
  have cZ2 := neg_le_abs (dotProduct (F.mulVec r) (F.mulVec z))
  rw [dotProduct_comm (F.mulVec r) (F.mulVec y)] at cY2
  rw [dotProduct_comm (F.mulVec r) (F.mulVec z)] at cZ2
  have hYY : l2Norm (F.mulVec y) ^ 2 ≤ θ * a * b + Λ * a := by
    rw [← dot_self_eq]
    have : Λ * a = θ * (L / Real.sqrt S) * a := by rw [hΛ]
    rw [dotProduct_comm (F.mulVec r) (F.mulVec y)] at bY
    linarith
  have hZZ : l2Norm (F.mulVec z) ^ 2 ≤ θ * a * b + Λ * b := by
    rw [← dot_self_eq]
    have : Λ * b = θ * (L / Real.sqrt S) * b := by rw [hΛ]
    rw [dotProduct_comm (F.mulVec r) (F.mulVec z)] at bZ
    have oZY' : |dotProduct (F.mulVec z) (F.mulVec y)| ≤ θ * a * b := by
      have := oZY; linarith [mul_comm a b, show θ * b * a = θ * a * b by ring]
    linarith
  -- linear inequalities for `a` and `b`
  have hA : (1 - δ) * a ≤ θ * b + Λ := by
    by_cases ha : a = 0
    · rw [ha, mul_zero]; positivity
    have hap : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    have : (1 - δ) * a * a ≤ (θ * b + Λ) * a := by nlinarith
    exact le_of_mul_le_mul_right this hap
  have hB : (1 - δ) * b ≤ θ * a + Λ := by
    by_cases hb : b = 0
    · rw [hb, mul_zero]; positivity
    have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have : (1 - δ) * b * b ≤ (θ * a + Λ) * b := by nlinarith
    exact le_of_mul_le_mul_right this hbp
  have h1d : 0 < 1 - δ := by linarith
  have key : (1 - δ - θ) * (1 - δ + θ) * a ≤ (1 - δ + θ) * Λ := by
    nlinarith [mul_le_mul_of_nonneg_left hA h1d.le, mul_le_mul_of_nonneg_left hB hθ0]
  have hpos : 0 < 1 - δ + θ := by linarith
  have : (1 - δ + θ) * ((1 - δ - θ) * a) ≤ (1 - δ + θ) * Λ := by
    have e1 : (1 - δ + θ) * ((1 - δ - θ) * a) = (1 - δ - θ) * (1 - δ + θ) * a := by ring
    rw [e1]; exact key
  exact le_of_mul_le_mul_left this hpos

end CandesTaoLem22

open CandesTaoLem22 in
theorem solution {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 3 * S ≤ m)
    (h : restrictedIsometryConst F S + restrictedOrthogonalityConst F S (2 * S) < 1)
    (T : Finset (Fin m)) (c : Fin m → ℝ) (hT : T.card ≤ S) (hc : SupportedOn c T) :
    ∃ w : Fin p → ℝ, w ∈ columnSpan F ∧ (∀ j ∈ T, dotProduct w (column F j) = c j) ∧
      ∀ j, j ∉ T →
        |dotProduct w (column F j)| ≤
          restrictedOrthogonalityConst F S S /
            ((1 - restrictedIsometryConst F S - restrictedOrthogonalityConst F S (2 * S)) *
              Real.sqrt S) * l2Norm c := by
  classical
  set δ := restrictedIsometryConst F S with hδdef
  set θ := restrictedOrthogonalityConst F S S with hθdef
  set θ₂ := restrictedOrthogonalityConst F S (2 * S) with hθ₂def
  have hδ0 : 0 ≤ δ := Real.sInf_nonneg fun x hx => hx.1
  have hθ0 : 0 ≤ θ := Real.sInf_nonneg fun x hx => hx.1
  have hθ₂0 : 0 ≤ θ₂ := Real.sInf_nonneg fun x hx => hx.1
  -- `θ_{S,S} ≤ θ_{S,2S}`
  have hθle : θ ≤ θ₂ := by
    have e1 : θ = sInf (TS F S S) := rfl
    have e2 : θ₂ = sInf (TS F S (2 * S)) := rfl
    rw [e1, e2]
    apply csInf_le_csInf ⟨0, fun _ hx => hx.1⟩ (TS_nonempty F S (2 * S))
    intro x hx
    refine ⟨hx.1, fun T T' hTT hT hT' c c' hc hc' => hx.2 T T' hTT hT (by omega) c c' hc hc'⟩
  have hgap₂ : 0 < 1 - δ - θ₂ := by linarith
  have hgap : 0 < 1 - δ - θ := by linarith
  have hsq : 0 < Real.sqrt (S : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hS)
  set M := θ / ((1 - δ - θ₂) * Real.sqrt S) * l2Norm c with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (div_nonneg hθ0 (mul_pos hgap₂ hsq).le) (l2_nonneg _)
  -- the Gram map and its range
  let Gl : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    (Matrix.mulVecLin F.transpose).comp (Matrix.mulVecLin F)
  have hGl : ∀ x, Gl x = F.transpose.mulVec (F.mulVec x) := fun x => rfl
  set K : Set (Fin m → ℝ) := (LinearMap.range Gl : Set (Fin m → ℝ)) with hK
  set C : Set (Fin m → ℝ) := Set.univ.pi
    (fun j => if j ∈ T then Set.Icc (c j) (c j) else Set.Icc (-M) M) with hC
  -- a feasible point exists
  have hex : ∃ g, g ∈ C ∧ g ∈ K := by
    by_contra hno
    push Not at hno
    have hdisj : Disjoint C K := Set.disjoint_left.mpr fun g hgC hgK => hno g hgC hgK
    have hCconv : Convex ℝ C := by
      apply convex_pi; intro j _; split_ifs <;> exact convex_Icc _ _
    have hCcomp : IsCompact C := by
      apply isCompact_univ_pi; intro j; split_ifs <;> exact isCompact_Icc
    have hKconv : Convex ℝ K := (LinearMap.range Gl).convex
    have hKclosed : IsClosed K := (LinearMap.range Gl).closed_of_finiteDimensional
    obtain ⟨f, u, v, hfC, huv, hfK⟩ :=
      geometric_hahn_banach_compact_closed hCconv hCcomp hKconv hKclosed hdisj
    -- `f` vanishes on the subspace `K`
    have hf0 : ∀ k ∈ K, f k = 0 := by
      intro k hk
      by_contra hne
      have hmem : ((v - 1) / f k) • k ∈ K := (LinearMap.range Gl).smul_mem _ hk
      have := hfK _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    have hv0 : v < 0 := by
      have := hfK 0 (LinearMap.range Gl).zero_mem
      rw [map_zero] at this; exact this
    -- coordinates of `f`
    set φ : Fin m → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hφdef
    have hfz : ∀ z : Fin m → ℝ, f z = ∑ i, z i * φ i := by
      intro z
      conv_lhs => rw [pi_eq_sum_univ z]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
    -- `φ ∈ ker F`
    have hFφ : F.mulVec φ = 0 := by
      have h1 := hf0 (Gl φ) (LinearMap.mem_range_self Gl φ)
      rw [hfz, hGl] at h1
      have h2 : dotProduct φ (F.transpose.mulVec (F.mulVec φ)) = 0 := by
        rw [← h1, dotProduct]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [dot_FF] at h2
      exact eq_zero_of_l2 _ (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
    have hN := nsp F S hS T hT φ hFφ (by rw [← hδdef, ← hθdef]; exact hgap)
    rw [← hδdef, ← hθdef] at hN
    set L := ∑ j ∈ Tᶜ, |φ j| with hL
    set a := l2Norm (rs T φ) with ha
    -- evaluate `f` at a corner of the box
    set b : Fin m → ℝ := fun j => if j ∈ T then c j else (if 0 ≤ φ j then M else -M) with hb
    have hbC : b ∈ C := by
      rw [hC, Set.mem_univ_pi]; intro j
      by_cases hj : j ∈ T
      · simp [hb, hj]
      · simp only [hb, hj, if_false]
        split_ifs <;> constructor <;> linarith
    have hfb := hfC b hbC
    rw [hfz] at hfb
    have hsplit : ∑ i, b i * φ i = ∑ i ∈ T, c i * φ i + M * L := by
      rw [← Finset.sum_add_sum_compl T, hL, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i hi => by simp [hb, hi]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_compl] at hi
        simp only [hb, hi, if_false]
        split_ifs with h0
        · rw [abs_of_nonneg h0]
        · push Not at h0; rw [abs_of_neg h0]; ring
    rw [hsplit] at hfb
    have hcs : -(a * l2Norm c) ≤ ∑ i ∈ T, c i * φ i := by
      have e : ∑ i ∈ T, c i * φ i = dotProduct (rs T φ) c := by
        rw [dotProduct]
        have : ∀ i, rs T φ i * c i = if i ∈ T then c i * φ i else 0 := by
          intro i; unfold rs; split_ifs <;> ring
        simp_rw [this]; rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [e]
      exact le_trans (neg_le_neg (abs_dot_le _ _)) (neg_abs_le _)
    -- `M L < a ‖c‖`, contradicting the null-space inequality
    have hlt : M * L < a * l2Norm c := by linarith
    have hN2 : (1 - δ - θ₂) * a ≤ θ * (L / Real.sqrt S) := by
      have : (1 - δ - θ₂) * a ≤ (1 - δ - θ) * a :=
        mul_le_mul_of_nonneg_right (by linarith) (l2_nonneg _)
      linarith
    have hge : a * l2Norm c ≤ M * L := by
      have hc0 := l2_nonneg c
      have e : M * L = θ * (L / Real.sqrt S) / (1 - δ - θ₂) * l2Norm c := by
        rw [hM]; field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_right _ hc0
      rw [le_div_iff₀ hgap₂]; linarith
    linarith
  obtain ⟨g, hgC, hgK⟩ := hex
  obtain ⟨x, hx⟩ := hgK
  refine ⟨F.mulVec x, ?_, ?_, ?_⟩
  · have : F.mulVec x = ∑ j, x j • column F j := by
      funext i
      simp only [Matrix.mulVec, dotProduct, column, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro j hj
    have hgj := (Set.mem_univ_pi.mp hgC) j
    simp only [hj, if_true, Set.mem_Icc] at hgj
    rw [dot_column_eq, ← hGl, hx]
    exact le_antisymm hgj.2 hgj.1
  · intro j hj
    have hgj := (Set.mem_univ_pi.mp hgC) j
    simp only [hj, if_false, Set.mem_Icc] at hgj
    rw [dot_column_eq, ← hGl, hx, abs_le]
    exact hgj
