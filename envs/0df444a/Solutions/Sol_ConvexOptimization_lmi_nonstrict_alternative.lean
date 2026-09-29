-- Prove2me | solution 1 for ConvexOptimization.lmi_nonstrict_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T05:18:32.802735+00:00
-- url     : https://prove2.me/submissions/5d9badc5-49f2-454e-b298-d1568a3d5f2d

import Mathlib

open scoped RealInnerProductSpace ENNReal MatrixOrder
open MeasureTheory
open Matrix
open Metric

namespace LMI2Aux

variable {nn : ℕ}

/-! ### Symmetric matrices, entrywise -/

theorem isSymm_apply {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) (i j : Fin nn) :
    M j i = M i j := congrFun (congrFun h i) j

theorem isSymm_of_apply {M : Matrix (Fin nn) (Fin nn) ℝ} (h : ∀ i j, M j i = M i j) :
    M.IsSymm := by
  ext i j; exact h i j

/-- For a symmetric `N`, `tr (M N)` is the entrywise pairing of `M` and `N`. -/
theorem trace_mul_eq_sum (M N : Matrix (Fin nn) (Fin nn) ℝ) (hN : N.IsSymm) :
    (M * N).trace = ∑ i, ∑ j, M i j * N i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [isSymm_apply hN i j]

/-! ### Identifying matrices with a Euclidean space -/

/-- The coordinatewise identification of `nn × nn` matrices with a Euclidean space.
It makes the separating-hyperplane theorem and the Riesz representation available. -/
noncomputable def toE (M : Matrix (Fin nn) (Fin nn) ℝ) :
    EuclideanSpace ℝ (Fin nn × Fin nn) := WithLp.toLp 2 (fun p => M p.1 p.2)

/-- The inverse identification. -/
def ofE (y : EuclideanSpace ℝ (Fin nn × Fin nn)) : Matrix (Fin nn) (Fin nn) ℝ :=
  Matrix.of fun i j => y (i, j)

@[simp] theorem ofE_toE (M : Matrix (Fin nn) (Fin nn) ℝ) : ofE (toE M) = M := rfl

@[simp] theorem toE_ofE (y : EuclideanSpace ℝ (Fin nn × Fin nn)) : toE (ofE y) = y := by
  ext p; rfl

theorem toE_add (M N : Matrix (Fin nn) (Fin nn) ℝ) : toE (M + N) = toE M + toE N := by
  ext p; rfl

theorem toE_smul (c : ℝ) (M : Matrix (Fin nn) (Fin nn) ℝ) : toE (c • M) = c • toE M := by
  ext p; rfl

theorem toE_neg (M : Matrix (Fin nn) (Fin nn) ℝ) : toE (-M) = -toE M := by
  ext p; rfl

theorem toE_sub (M N : Matrix (Fin nn) (Fin nn) ℝ) : toE (M - N) = toE M - toE N := by
  ext p; rfl

theorem toE_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin nn) (Fin nn) ℝ) :
    toE (∑ i ∈ s, f i) = ∑ i ∈ s, toE (f i) := by
  classical
  induction s using Finset.induction with
  | empty => ext p; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toE_add, ih]

theorem inner_toE (M N : Matrix (Fin nn) (Fin nn) ℝ) :
    ⟪toE M, toE N⟫ = ∑ i, ∑ j, M i j * N i j := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp [toE, mul_comm]

/-! ### Quadratic forms -/

theorem quad_eq_sum (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, M i j * (x i * x j) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem quad_eq_inner (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ⟪toE M, toE (Matrix.vecMulVec x x)⟫ := by
  rw [inner_toE, quad_eq_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl

theorem vecMulVec_isSymm (x : Fin nn → ℝ) : (Matrix.vecMulVec x x).IsSymm :=
  isSymm_of_apply fun i j => by simp [Matrix.vecMulVec_apply, mul_comm]

theorem dotProduct_self_nonneg (x : Fin nn → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem dotProduct_self_pos {x : Fin nn → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  rw [dotProduct]
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr (by simpa using hi)

theorem norm_toE_vecMulVec (x : Fin nn → ℝ) :
    ‖toE (Matrix.vecMulVec x x)‖ = x ⬝ᵥ x := by
  have hsq : ‖toE (Matrix.vecMulVec x x)‖ ^ 2 = (x ⬝ᵥ x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toE]
    have h1 : ∀ i j : Fin nn, Matrix.vecMulVec x x i j * Matrix.vecMulVec x x i j
        = (x i * x i) * (x j * x j) := by
      intro i j; simp [Matrix.vecMulVec_apply]; ring
    calc ∑ i, ∑ j, Matrix.vecMulVec x x i j * Matrix.vecMulVec x x i j
        = ∑ i, ∑ j, (x i * x i) * (x j * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
      _ = (∑ i, x i * x i) * (∑ j, x j * x j) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = (x ⬝ᵥ x) ^ 2 := by rw [dotProduct]; ring
  have h1 : (0 : ℝ) ≤ ‖toE (Matrix.vecMulVec x x)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ x ⬝ᵥ x := dotProduct_self_nonneg x
  nlinarith [hsq, h1, h2]

/-- Cauchy–Schwarz for the quadratic form: the perturbation of a quadratic form by
`Δ` is controlled by the Euclidean norm of `Δ`. -/
theorem abs_quad_le (Δ : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    |x ⬝ᵥ (Δ *ᵥ x)| ≤ ‖toE Δ‖ * (x ⬝ᵥ x) := by
  rw [quad_eq_inner, ← norm_toE_vecMulVec x]
  exact abs_real_inner_le_norm _ _

/-! ### Uniform positivity of a positive definite quadratic form -/

theorem norm_toLp (x : Fin nn → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin nn))‖ = Real.sqrt (x ⬝ᵥ x) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq_abs, pow_two]

theorem quad_smul (M : Matrix (Fin nn) (Fin nn) ℝ) (t : ℝ) (x : Fin nn → ℝ) :
    (t • x) ⬝ᵥ (M *ᵥ (t • x)) = t ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [quad_eq_sum, quad_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

theorem dot_smul_self (t : ℝ) (x : Fin nn → ℝ) : (t • x) ⬝ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ x) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A positive definite quadratic form dominates a positive multiple of `‖x‖²`.
This is the compactness step: the form attains a positive minimum on the unit sphere. -/
theorem exists_pos_lower (M : Matrix (Fin nn) (Fin nn) ℝ)
    (hM : ∀ x : Fin nn → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin nn → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by
  classical
  rcases Nat.eq_zero_or_pos nn with h0 | hpos
  · subst h0
    exact ⟨1, one_pos, fun x => by simp [dotProduct]⟩
  · set φ : EuclideanSpace ℝ (Fin nn) → ℝ :=
      fun u => (WithLp.ofLp u) ⬝ᵥ (M *ᵥ (WithLp.ofLp u)) with hφdef
    have hcont : Continuous φ := by
      have hrw : φ = fun u : EuclideanSpace ℝ (Fin nn) => ∑ i, ∑ j, M i j * (u i * u j) := by
        funext u; rw [hφdef]; exact quad_eq_sum M _
      rw [hrw]
      refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
      exact continuous_const.mul
        ((PiLp.continuous_apply 2 (fun _ : Fin nn => ℝ) i).mul
          (PiLp.continuous_apply 2 (fun _ : Fin nn => ℝ) j))
    have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin nn)) 1).Nonempty := by
      refine ⟨EuclideanSpace.single ⟨0, hpos⟩ 1, ?_⟩
      simp
    obtain ⟨u₀, hu₀mem, hu₀min⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin nn)) 1).exists_isMinOn hne hcont.continuousOn
    have hu₀norm : ‖u₀‖ = 1 := mem_sphere_zero_iff_norm.mp hu₀mem
    have hu₀ne : (WithLp.ofLp u₀ : Fin nn → ℝ) ≠ 0 := by
      intro hz
      have : u₀ = 0 := by ext i; exact congrFun hz i
      rw [this] at hu₀norm; simp at hu₀norm
    refine ⟨φ u₀, hM _ hu₀ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [dotProduct]
    · have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
      set r : ℝ := Real.sqrt (x ⬝ᵥ x) with hrdef
      have hrpos : 0 < r := Real.sqrt_pos.mpr hxx
      have hr2 : r ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hxx.le
      set u : EuclideanSpace ℝ (Fin nn) := WithLp.toLp 2 (r⁻¹ • x) with hudef
      have hunorm : ‖u‖ = 1 := by
        rw [hudef, norm_toLp, dot_smul_self, ← hr2]
        rw [show (r⁻¹) ^ 2 * r ^ 2 = 1 by field_simp]
        exact Real.sqrt_one
      have hmem : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin nn)) 1 :=
        mem_sphere_zero_iff_norm.mpr hunorm
      have hkey : φ u₀ ≤ φ u := hu₀min hmem
      have hφu : φ u = (r⁻¹) ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
        rw [hφdef]
        exact quad_smul M (r⁻¹) x
      rw [hφu] at hkey
      have hrne : r ≠ 0 := ne_of_gt hrpos
      have hmul : φ u₀ * r ^ 2 ≤ (r⁻¹ ^ 2 * (x ⬝ᵥ (M *ᵥ x))) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      have hsimp : (r⁻¹ ^ 2 * (x ⬝ᵥ (M *ᵥ x))) * r ^ 2 = x ⬝ᵥ (M *ᵥ x) := by
        field_simp
      rw [hsimp, hr2] at hmul
      exact hmul

/-! ### Elementary algebra of quadratic forms -/

theorem quad_add (M N : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((M + N) *ᵥ x) = x ⬝ᵥ (M *ᵥ x) + x ⬝ᵥ (N *ᵥ x) := by
  rw [Matrix.add_mulVec, dotProduct_add]

theorem quad_neg (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((-M) *ᵥ x) = -(x ⬝ᵥ (M *ᵥ x)) := by
  rw [Matrix.neg_mulVec, dotProduct_neg]

theorem quad_smul_mat (c : ℝ) (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((c • M) *ᵥ x) = c * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [quad_eq_sum, quad_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [Matrix.smul_apply]; ring

theorem quad_one (x : Fin nn → ℝ) : x ⬝ᵥ ((1 : Matrix (Fin nn) (Fin nn) ℝ) *ᵥ x) = x ⬝ᵥ x := by
  rw [Matrix.one_mulVec]

theorem quad_vecMulVec (v x : Fin nn → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec v v *ᵥ x) = (v ⬝ᵥ x) ^ 2 := by
  rw [quad_eq_sum]
  calc ∑ i, ∑ j, Matrix.vecMulVec v v i j * (x i * x j)
      = ∑ i, ∑ j, (v i * x i) * (v j * x j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          simp [Matrix.vecMulVec_apply]; ring
    _ = (∑ i, v i * x i) * (∑ j, v j * x j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = (v ⬝ᵥ x) ^ 2 := by rw [dotProduct]; ring

theorem isHermitian_of_isSymm {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) :
    M.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact isSymm_apply h i j

/-! ### Trace positivity -/

theorem trace_mul_sq (P S : Matrix (Fin nn) (Fin nn) ℝ) (hS : S.IsSymm) :
    (P * (S * S)).trace = ∑ k, (fun i => S k i) ⬝ᵥ (P *ᵥ (fun i => S k i)) := by
  have hSS : (S * S).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, hS.eq]
  rw [trace_mul_eq_sum P (S * S) hSS]
  have hz : ∀ i j, (S * S) i j = ∑ k, S k i * S k j := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [isSymm_apply hS i k]
  calc ∑ i, ∑ j, P i j * (S * S) i j
      = ∑ i, ∑ j, ∑ k, P i j * (S k i * S k j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hz i j, Finset.mul_sum]
    _ = ∑ i, ∑ k, ∑ j, P i j * (S k i * S k j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, P i j * (S k i * S k j) := Finset.sum_comm
    _ = ∑ k, (fun i => S k i) ⬝ᵥ (P *ᵥ (fun i => S k i)) :=
        Finset.sum_congr rfl fun k _ => (quad_eq_sum P (fun i => S k i)).symm

/-- `tr(PZ) > 0` for `P` positive definite and `Z` positive semidefinite and nonzero. -/
theorem trace_mul_pos (P Z : Matrix (Fin nn) (Fin nn) ℝ) (hP : P.PosDef)
    (hZ : Z.PosSemidef) (hZne : Z ≠ 0) : 0 < (P * Z).trace := by
  classical
  obtain ⟨c, hc, hlow⟩ := exists_pos_lower P (fun x hx => by
    simpa using hP.dotProduct_mulVec_pos hx)
  have hSpsd : (CFC.sqrt Z).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Z)
  have hSsq : CFC.sqrt Z * CFC.sqrt Z = Z := by
    have h := CFC.sq_sqrt Z (Matrix.nonneg_iff_posSemidef.mpr hZ)
    rwa [sq] at h
  set S : Matrix (Fin nn) (Fin nn) ℝ := CFC.sqrt Z with hSdef
  have hSsymm : S.IsSymm := hSpsd.isHermitian
  have hSne : S ≠ 0 := by
    intro h; apply hZne; rw [← hSsq, h, Matrix.zero_mul]
  obtain ⟨k0, i0, hk0⟩ : ∃ k i, S k i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hSne (by ext k i; simp [hcon k i])
  rw [← hSsq, trace_mul_sq P S hSsymm]
  refine lt_of_lt_of_le ?_ (Finset.sum_le_sum fun k _ => hlow (fun i => S k i))
  refine Finset.sum_pos' (fun k _ => mul_nonneg hc.le (dotProduct_self_nonneg _))
    ⟨k0, Finset.mem_univ k0, ?_⟩
  exact mul_pos hc (dotProduct_self_pos (fun h => hk0 (congrFun h i0)))


/-! ### The positive semidefinite cone -/

/-- Matrices with nonnegative quadratic form; on symmetric matrices this is the
positive semidefinite cone. -/
def Kcone (nn : ℕ) : Set (EuclideanSpace ℝ (Fin nn × Fin nn)) :=
  {y | ∀ x : Fin nn → ℝ, 0 ≤ x ⬝ᵥ ((ofE y) *ᵥ x)}

theorem convex_Kcone : Convex ℝ (Kcone nn) := by
  rintro y₁ h₁ y₂ h₂ a b ha hb hab x
  have hof : ofE (a • y₁ + b • y₂) = a • ofE y₁ + b • ofE y₂ := rfl
  rw [hof, quad_add, quad_smul_mat, quad_smul_mat]
  exact add_nonneg (mul_nonneg ha (h₁ x)) (mul_nonneg hb (h₂ x))

theorem smul_mem_Kcone {t : ℝ} (ht : 0 ≤ t) {y : EuclideanSpace ℝ (Fin nn × Fin nn)}
    (hy : y ∈ Kcone nn) : t • y ∈ Kcone nn := by
  intro x
  have hof : ofE (t • y) = t • ofE y := rfl
  rw [hof, quad_smul_mat]
  exact mul_nonneg ht (hy x)

theorem add_mem_Kcone {y z : EuclideanSpace ℝ (Fin nn × Fin nn)}
    (hy : y ∈ Kcone nn) (hz : z ∈ Kcone nn) : y + z ∈ Kcone nn := by
  intro x
  have hof : ofE (y + z) = ofE y + ofE z := rfl
  rw [hof, quad_add]
  exact add_nonneg (hy x) (hz x)

theorem zero_mem_Kcone : (0 : EuclideanSpace ℝ (Fin nn × Fin nn)) ∈ Kcone nn := by
  intro x
  have h : ofE (0 : EuclideanSpace ℝ (Fin nn × Fin nn)) = 0 := rfl
  rw [h]
  simp [Matrix.zero_mulVec, dotProduct]

theorem isClosed_Kcone : IsClosed (Kcone nn) := by
  have hrw : Kcone nn
      = ⋂ x : Fin nn → ℝ, {y : EuclideanSpace ℝ (Fin nn × Fin nn) |
          0 ≤ (inner ℝ y (toE (Matrix.vecMulVec x x)) : ℝ)} := by
    ext y
    simp only [Kcone, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h x; have := h x; rwa [quad_eq_inner, toE_ofE] at this
    · intro h x; have := h x; rwa [quad_eq_inner, toE_ofE]
  rw [hrw]
  exact isClosed_iInter fun x =>
    isClosed_le continuous_const (continuous_id.inner continuous_const)

theorem mem_Kcone_iff {M : Matrix (Fin nn) (Fin nn) ℝ} (hM : M.IsSymm) :
    toE M ∈ Kcone nn ↔ M.PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_isSymm hM) fun x => ?_
    rw [show (star x : Fin nn → ℝ) = x from star_trivial x]
    have := h x; rwa [ofE_toE] at this
  · intro h x
    rw [ofE_toE]
    have := h.dotProduct_mulVec_nonneg x
    rwa [show (star x : Fin nn → ℝ) = x from star_trivial x] at this

/-- `tr(PZ) ≥ 0` for two positive semidefinite matrices. -/
theorem trace_mul_nonneg (P Z : Matrix (Fin nn) (Fin nn) ℝ) (hP : P.PosSemidef)
    (hZ : Z.PosSemidef) : 0 ≤ (P * Z).trace := by
  have hSpsd : (CFC.sqrt Z).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Z)
  have hSsq : CFC.sqrt Z * CFC.sqrt Z = Z := by
    have h := CFC.sq_sqrt Z (Matrix.nonneg_iff_posSemidef.mpr hZ)
    rwa [sq] at h
  rw [← hSsq, trace_mul_sq P (CFC.sqrt Z) hSpsd.isHermitian]
  refine Finset.sum_nonneg fun k _ => ?_
  have h := hP.dotProduct_mulVec_nonneg (fun i => CFC.sqrt Z k i)
  rwa [show star (fun i => CFC.sqrt Z k i) = (fun i => CFC.sqrt Z k i) from
    star_trivial _] at h

/-! ### A subspace plus a closed cone meeting it only at the origin is closed -/

/-- The uniform bound `δ‖w‖ ≤ ‖w + p‖`, obtained by minimizing the distance from
`-w` to the cone over the (compact) unit sphere of the subspace. -/
theorem exists_delta (W : Submodule ℝ (EuclideanSpace ℝ (Fin nn × Fin nn)))
    (hW : ∀ w ∈ W, -w ∈ Kcone nn → w = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ W, ∀ p ∈ Kcone nn, δ * ‖w‖ ≤ ‖w + p‖ := by
  classical
  have hKne : (Kcone nn).Nonempty := ⟨0, zero_mem_Kcone⟩
  set φ : EuclideanSpace ℝ (Fin nn × Fin nn) → ℝ :=
    fun w => Metric.infDist (-w) (Kcone nn) with hφdef
  have hφcont : Continuous φ :=
    (Metric.lipschitz_infDist_pt (Kcone nn)).continuous.comp continuous_neg
  have hφle : ∀ (w : EuclideanSpace ℝ (Fin nn × Fin nn)), ∀ p ∈ Kcone nn, φ w ≤ ‖w + p‖ := by
    intro w p hp
    have h := Metric.infDist_le_dist_of_mem (x := -w) hp
    rwa [dist_eq_norm, show -w - p = -(w + p) by abel, norm_neg] at h
  set B : Set (EuclideanSpace ℝ (Fin nn × Fin nn)) := (W : Set _) ∩ Metric.sphere 0 1 with hBdef
  have hBcompact : IsCompact B :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin nn × Fin nn)) 1).inter_left
      W.closed_of_finiteDimensional
  have hφpos : ∀ w ∈ B, 0 < φ w := by
    intro w hw
    rcases lt_or_eq_of_le (Metric.infDist_nonneg (x := -w) (s := Kcone nn)) with h | h
    · exact h
    · exfalso
      have hmem : -w ∈ Kcone nn := (isClosed_Kcone.mem_iff_infDist_zero hKne).mpr h.symm
      have hz := hW w hw.1 hmem
      have hn : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw.2
      rw [hz] at hn; simp at hn
  rcases B.eq_empty_or_nonempty with hBe | hBn
  · refine ⟨1, one_pos, fun w hw p hp => ?_⟩
    have hw0 : w = 0 := by
      by_contra hne
      have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hne
      have hmem : ‖w‖⁻¹ • w ∈ B := by
        refine ⟨W.smul_mem _ hw, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (ne_of_gt hnw)]
      rw [hBe] at hmem; exact hmem
    rw [hw0]; simp
  · obtain ⟨w₀, hw₀B, hw₀min⟩ := hBcompact.exists_isMinOn hBn hφcont.continuousOn
    refine ⟨φ w₀, hφpos w₀ hw₀B, fun w hw p hp => ?_⟩
    by_cases hw0 : w = 0
    · rw [hw0]; simp
    · have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hmem : ‖w‖⁻¹ • w ∈ B := by
        refine ⟨W.smul_mem _ hw, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (ne_of_gt hnw)]
      have h3 : φ w₀ ≤ φ (‖w‖⁻¹ • w) := hw₀min hmem
      have h1 : φ (‖w‖⁻¹ • w) ≤ ‖‖w‖⁻¹ • w + ‖w‖⁻¹ • p‖ :=
        hφle _ _ (smul_mem_Kcone (by positivity) hp)
      have h2 : ‖‖w‖⁻¹ • w + ‖w‖⁻¹ • p‖ = ‖w‖⁻¹ * ‖w + p‖ := by
        rw [← smul_add, norm_smul, norm_inv, norm_norm]
      rw [h2] at h1
      have h4 : φ w₀ ≤ ‖w‖⁻¹ * ‖w + p‖ := le_trans h3 h1
      have h5 := mul_le_mul_of_nonneg_right h4 hnw.le
      rwa [inv_mul_eq_div, div_mul_eq_mul_div, mul_div_assoc,
        div_self (ne_of_gt hnw), mul_one] at h5

theorem isClosed_sum (W : Submodule ℝ (EuclideanSpace ℝ (Fin nn × Fin nn)))
    (hW : ∀ w ∈ W, -w ∈ Kcone nn → w = 0) :
    IsClosed {y : EuclideanSpace ℝ (Fin nn × Fin nn) | ∃ w ∈ W, ∃ p ∈ Kcone nn, y = w + p} := by
  classical
  obtain ⟨δ, hδ, hbound⟩ := exists_delta W hW
  refine IsSeqClosed.isClosed ?_
  intro y ylim hy hlim
  choose w hwW p hpK hyeq using hy
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto y hlim).subset_closedBall
    (0 : EuclideanSpace ℝ (Fin nn × Fin nn))
  have hwb : ∀ j, w j ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin nn × Fin nn)) (R / δ) := by
    intro j
    have h1 : δ * ‖w j‖ ≤ ‖w j + p j‖ := hbound _ (hwW j) _ (hpK j)
    have h2 : ‖y j‖ ≤ R := by
      have := hR (Set.mem_range_self j)
      simpa [Metric.mem_closedBall, dist_eq_norm] using this
    rw [← hyeq j] at h1
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [le_div_iff₀ hδ]
    linarith
  obtain ⟨a, -, ψ, hψ, hconv⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin nn × Fin nn))) (r := R / δ))
    hwb
  have haW : a ∈ W := W.closed_of_finiteDimensional.mem_of_tendsto hconv
    (Filter.Eventually.of_forall fun j => hwW (ψ j))
  have hplim : Filter.Tendsto (fun j => p (ψ j)) Filter.atTop (nhds (ylim - a)) := by
    have hy' : Filter.Tendsto (fun j => y (ψ j)) Filter.atTop (nhds ylim) :=
      hlim.comp hψ.tendsto_atTop
    have hrw : (fun j => p (ψ j)) = fun j => y (ψ j) - w (ψ j) := by
      funext j; rw [hyeq (ψ j)]; abel
    rw [hrw]
    exact hy'.sub hconv
  have hpa : ylim - a ∈ Kcone nn := isClosed_Kcone.mem_of_tendsto hplim
    (Filter.Eventually.of_forall fun j => hpK (ψ j))
  exact ⟨a, haW, ylim - a, hpa, by abel⟩

end LMI2Aux

open LMI2Aux in
theorem solution {n nn : ℕ}
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm)
    (hCQ : ∀ v : Fin n → ℝ, (∑ i, v i • F i).PosSemidef → ∑ i, v i • F i = 0) :
    (∃ x : Fin n → ℝ, (-(G + ∑ i, x i • F i)).PosSemidef) ↔
      ¬∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧
        (∀ i, ((F i) * Z).trace = 0) ∧ 0 < (G * Z).trace := by
  classical
  have hFsum : ∀ (y : Fin n → ℝ) (i j : Fin nn),
      (∑ k, y k • F k) i j = ∑ k, y k * F k i j := by
    intro y i j
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hAapply : ∀ (y : Fin n → ℝ) (i j : Fin nn),
      (G + ∑ k, y k • F k) i j = G i j + ∑ k, y k * F k i j := by
    intro y i j; rw [Matrix.add_apply, hFsum]
  have hAsymm : ∀ y : Fin n → ℝ, (G + ∑ k, y k • F k).IsSymm := by
    intro y
    refine isSymm_of_apply fun i j => ?_
    rw [hAapply, hAapply, isSymm_apply hG i j]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [isSymm_apply (hF k) i j]
  have hVsymm : ∀ y : Fin n → ℝ, (∑ k, y k • F k).IsSymm := by
    intro y
    refine isSymm_of_apply fun i j => ?_
    rw [hFsum, hFsum]
    exact Finset.sum_congr rfl fun k _ => by rw [isSymm_apply (hF k) i j]
  constructor
  · -- Weak alternatives: both systems cannot hold.
    rintro ⟨x, hx⟩ ⟨Z, hZ, hFZ, hGZ⟩
    have hnn := trace_mul_nonneg _ Z hx hZ
    have hexpand : ((-(G + ∑ i, x i • F i)) * Z).trace
        = -((G * Z).trace) - ∑ i, x i * ((F i * Z).trace) := by
      rw [Matrix.neg_mul, Matrix.trace_neg, Matrix.add_mul, Matrix.trace_add,
        Finset.sum_mul, Matrix.trace_sum]
      have hs : ∀ i, ((x i • F i) * Z).trace = x i * ((F i * Z).trace) := by
        intro i; rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [Finset.sum_congr rfl fun i _ => hs i]
      ring
    rw [hexpand, Finset.sum_eq_zero fun i _ => by rw [hFZ i, mul_zero]] at hnn
    linarith
  · -- Strong alternatives: separate `-G` from the (closed) sum of the span and the cone.
    intro hnoZ
    by_contra hno
    push_neg at hno
    apply hnoZ
    set W : Submodule ℝ (EuclideanSpace ℝ (Fin nn × Fin nn)) :=
      Submodule.span ℝ (Set.range (fun i => toE (F i))) with hWdef
    have hWmem : ∀ v : Fin n → ℝ, toE (∑ i, v i • F i) ∈ W := by
      intro v
      rw [toE_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [toE_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hWrepr : ∀ w ∈ W, ∃ v : Fin n → ℝ, w = toE (∑ i, v i • F i) := by
      intro w hw
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
      refine ⟨c, ?_⟩
      rw [toE_sum, ← hc]
      exact Finset.sum_congr rfl fun i _ => (toE_smul _ _).symm
    have hWcond : ∀ w ∈ W, -w ∈ Kcone nn → w = 0 := by
      intro w hw hneg
      obtain ⟨v, rfl⟩ := hWrepr w hw
      rw [← toE_neg] at hneg
      have hsym : (-(∑ i, v i • F i)).IsSymm :=
        isSymm_of_apply fun i j => by
          simp only [Matrix.neg_apply]; rw [isSymm_apply (hVsymm v) i j]
      have hpsd := (mem_Kcone_iff hsym).mp hneg
      have heq : ∑ i, (-v) i • F i = -(∑ i, v i • F i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by simp
      rw [← heq] at hpsd
      have hz := hCQ (-v) hpsd
      rw [heq] at hz
      rw [neg_eq_zero.mp hz]
      ext q; rfl
    set T : Set (EuclideanSpace ℝ (Fin nn × Fin nn)) :=
      {y | ∃ w ∈ W, ∃ p ∈ Kcone nn, y = w + p} with hTdef
    have hTclosed : IsClosed T := isClosed_sum W hWcond
    have hTconv : Convex ℝ T := by
      rintro _ ⟨w₁, hw₁, p₁, hp₁, rfl⟩ _ ⟨w₂, hw₂, p₂, hp₂, rfl⟩ a b ha hb hab
      refine ⟨a • w₁ + b • w₂, W.add_mem (W.smul_mem _ hw₁) (W.smul_mem _ hw₂),
        a • p₁ + b • p₂, add_mem_Kcone (smul_mem_Kcone ha hp₁) (smul_mem_Kcone hb hp₂), ?_⟩
      rw [smul_add, smul_add]; abel
    have hTmem : (0 : EuclideanSpace ℝ (Fin nn × Fin nn)) ∈ T :=
      ⟨0, W.zero_mem, 0, zero_mem_Kcone, by rw [add_zero]⟩
    have hnotmem : -(toE G) ∉ T := by
      rintro ⟨w, hw, p, hp, heq⟩
      obtain ⟨v, rfl⟩ := hWrepr w hw
      refine hno v ?_
      have hpeq : p = toE (-(G + ∑ i, v i • F i)) := by
        have hsub : p = -(toE G) - toE (∑ i, v i • F i) := by rw [heq]; abel
        rw [hsub, ← toE_neg, ← toE_sub]
        congr 1
        rw [neg_add]
        abel
      rw [hpeq] at hp
      refine (mem_Kcone_iff ?_).mp hp
      exact isSymm_of_apply fun i j => by
        simp only [Matrix.neg_apply]; rw [isSymm_apply (hAsymm v) i j]
    obtain ⟨Φ, u, hΦT, hΦpt⟩ := geometric_hahn_banach_closed_point hTconv hTclosed hnotmem
    have hu : 0 < u := by
      have := hΦT 0 hTmem
      rwa [map_zero] at this
    have hΦW : ∀ w ∈ W, Φ w = 0 := by
      intro w hw
      by_contra hne
      have hmem : ((u + 1) / Φ w) • w ∈ T :=
        ⟨((u + 1) / Φ w) • w, W.smul_mem _ hw, 0, zero_mem_Kcone, by rw [add_zero]⟩
      have h := hΦT _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
      linarith
    have hΦK : ∀ p ∈ Kcone nn, Φ p ≤ 0 := by
      intro p hp
      by_contra hcon
      push_neg at hcon
      have hpos : 0 < (u + 1) / Φ p := div_pos (by linarith) hcon
      have hmem : (((u + 1) / Φ p) • p) ∈ T :=
        ⟨0, W.zero_mem, ((u + 1) / Φ p) • p, smul_mem_Kcone hpos.le hp, by rw [zero_add]⟩
      have h := hΦT _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_gt hcon)] at h
      linarith
    -- Riesz representation, symmetrized and negated.
    set zv : EuclideanSpace ℝ (Fin nn × Fin nn) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin nn × Fin nn))).symm Φ with hzvdef
    have hzv : ∀ y, ⟪zv, y⟫ = Φ y := by
      intro y; rw [hzvdef, InnerProductSpace.toDual_symm_apply]
    set Wm : Matrix (Fin nn) (Fin nn) ℝ := ofE zv with hWmdef
    have hWmE : toE Wm = zv := by rw [hWmdef, toE_ofE]
    set Z : Matrix (Fin nn) (Fin nn) ℝ := -((2 : ℝ)⁻¹ • (Wm + Wmᵀ)) with hZdef
    have hZsymm : Z.IsSymm := by
      unfold Matrix.IsSymm
      rw [hZdef, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_add,
        Matrix.transpose_transpose, add_comm Wmᵀ Wm]
    have hpair : ∀ M : Matrix (Fin nn) (Fin nn) ℝ, M.IsSymm → (M * Z).trace = -Φ (toE M) := by
      intro M hM
      have hzM : Φ (toE M) = ∑ i, ∑ j, Wm i j * M i j := by
        rw [← hzv (toE M), ← hWmE, inner_toE]
      have hswap : ∑ i, ∑ j, Wm j i * M i j = ∑ i, ∑ j, Wm i j * M i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [isSymm_apply hM i j]
      have hZij : ∀ i j, M i j * Z i j = -((Wm i j * M i j + Wm j i * M i j) / 2) := by
        intro i j
        simp only [hZdef, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
          Matrix.transpose_apply, smul_eq_mul]
        ring
      have hinner : ∀ i : Fin nn, ∑ j, -((Wm i j * M i j + Wm j i * M i j) / 2)
          = -(((∑ j, Wm i j * M i j) + (∑ j, Wm j i * M i j)) / 2) := by
        intro i
        rw [Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
      rw [trace_mul_eq_sum M Z hZsymm, hzM,
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hZij i j,
        Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i,
        Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hswap]
      ring
    refine ⟨Z, ?_, fun i => ?_, ?_⟩
    · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_isSymm hZsymm) ?_
      intro v
      rw [show (star v : Fin nn → ℝ) = v from star_trivial v]
      have hq : v ⬝ᵥ (Z *ᵥ v) = (Matrix.vecMulVec v v * Z).trace := by
        rw [trace_mul_eq_sum _ Z hZsymm, quad_eq_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          simp [Matrix.vecMulVec_apply]; ring
      rw [hq, hpair _ (vecMulVec_isSymm v), neg_nonneg]
      refine hΦK _ fun x => ?_
      rw [ofE_toE, quad_vecMulVec]
      positivity
    · rw [hpair _ (hF i), hΦW _ (Submodule.subset_span ⟨i, rfl⟩), neg_zero]
    · rw [hpair _ hG]
      have hneg : Φ (-(toE G)) = -Φ (toE G) := map_neg Φ _
      linarith [hΦpt, hneg]
