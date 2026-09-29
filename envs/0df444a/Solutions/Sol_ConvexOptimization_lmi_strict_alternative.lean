-- Prove2me | solution 1 for ConvexOptimization.lmi_strict_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T05:00:21.960316+00:00
-- url     : https://prove2.me/submissions/678de24a-5bb7-48f8-9bf1-0b542391573d

import Mathlib

open scoped RealInnerProductSpace ENNReal MatrixOrder
open MeasureTheory
open Matrix

namespace LMIAux

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

/-! ### The open convex cone of negative definite matrices -/

/-- The negative definite matrices, seen inside the Euclidean space of all matrices. -/
def NDset (nn : ℕ) : Set (EuclideanSpace ℝ (Fin nn × Fin nn)) :=
  {y | ∀ x : Fin nn → ℝ, x ≠ 0 → x ⬝ᵥ ((ofE y) *ᵥ x) < 0}

theorem mem_NDset_iff {y : EuclideanSpace ℝ (Fin nn × Fin nn)} :
    y ∈ NDset nn ↔ ∀ x : Fin nn → ℝ, x ≠ 0 → x ⬝ᵥ ((ofE y) *ᵥ x) < 0 := Iff.rfl

theorem isOpen_NDset : IsOpen (NDset nn) := by
  rw [Metric.isOpen_iff]
  intro y hy
  obtain ⟨c, hc, hclow⟩ := exists_pos_lower (-(ofE y)) (fun x hx => by
    rw [quad_neg]; linarith [hy x hx])
  refine ⟨c, hc, fun z hz => ?_⟩
  intro x hx
  have hzy : ‖z - y‖ < c := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
  have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
  have hlow := hclow x
  rw [quad_neg] at hlow
  have hdecomp : ofE y + (ofE z - ofE y) = ofE z := by abel
  have hsplit : x ⬝ᵥ ((ofE z) *ᵥ x)
      = x ⬝ᵥ ((ofE y) *ᵥ x) + x ⬝ᵥ ((ofE z - ofE y) *ᵥ x) := by
    rw [← quad_add, hdecomp]
  have hbound : |x ⬝ᵥ ((ofE z - ofE y) *ᵥ x)| ≤ ‖z - y‖ * (x ⬝ᵥ x) := by
    have h := abs_quad_le (ofE z - ofE y) x
    rwa [toE_sub, toE_ofE, toE_ofE] at h
  have h1 : x ⬝ᵥ ((ofE z - ofE y) *ᵥ x) ≤ ‖z - y‖ * (x ⬝ᵥ x) :=
    le_trans (le_abs_self _) hbound
  have h2 : ‖z - y‖ * (x ⬝ᵥ x) < c * (x ⬝ᵥ x) :=
    mul_lt_mul_of_pos_right hzy hxx
  rw [hsplit]
  linarith

theorem convex_NDset : Convex ℝ (NDset nn) := by
  rintro y₁ h₁ y₂ h₂ a b ha hb hab x hx
  have hof : ofE (a • y₁ + b • y₂) = a • ofE y₁ + b • ofE y₂ := rfl
  rw [show x ⬝ᵥ ((ofE (a • y₁ + b • y₂)) *ᵥ x)
      = a * (x ⬝ᵥ ((ofE y₁) *ᵥ x)) + b * (x ⬝ᵥ ((ofE y₂) *ᵥ x)) by
    rw [hof, quad_add, quad_smul_mat, quad_smul_mat]]
  have p1 := h₁ x hx
  have p2 := h₂ x hx
  rcases eq_or_lt_of_le ha with h | h
  · have hb1 : b = 1 := by linarith
    rw [← h, hb1]; simpa using p2
  · nlinarith

theorem smul_mem_NDset {t : ℝ} (ht : 0 < t) {y : EuclideanSpace ℝ (Fin nn × Fin nn)}
    (hy : y ∈ NDset nn) : t • y ∈ NDset nn := by
  intro x hx
  have hof : ofE (t • y) = t • ofE y := rfl
  rw [hof, quad_smul_mat]
  exact mul_neg_of_pos_of_neg ht (hy x hx)

theorem negOne_mem_NDset (hnn : 0 < nn) :
    toE (-1 : Matrix (Fin nn) (Fin nn) ℝ) ∈ NDset nn := by
  intro x hx
  rw [ofE_toE, quad_neg, quad_one]
  exact neg_lt_zero.mpr (dotProduct_self_pos hx)

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

/-! ### The separation step -/

/-- **Example 5.14, hard direction.** If the strict LMI `G + Σ xᵢFᵢ ≺ 0` is infeasible,
the affine family `{G + Σ xᵢFᵢ}` misses the open convex cone of negative definite
matrices, and a separating hyperplane produces the dual certificate `Z`. -/
theorem separation {n nn : ℕ} (hnn : 0 < nn)
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm)
    (hno : ∀ x : Fin n → ℝ, ¬ (-(G + ∑ i, x i • F i)).PosDef) :
    ∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧
      (∀ i, ((F i) * Z).trace = 0) ∧ 0 ≤ (G * Z).trace := by
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
  -- The affine family, transported to the Euclidean space of matrices.
  set L : Set (EuclideanSpace ℝ (Fin nn × Fin nn)) :=
    Set.range (fun y : Fin n → ℝ => toE (G + ∑ k, y k • F k)) with hLdef
  have hLconv : Convex ℝ L := by
    rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩ a b ha hb hab
    refine ⟨a • x₁ + b • x₂, ?_⟩
    have hb1 : b = 1 - a := by linarith
    subst hb1
    have hmat : (G + ∑ k, (a • x₁ + (1 - a) • x₂) k • F k)
        = a • (G + ∑ k, x₁ k • F k) + (1 - a) • (G + ∑ k, x₂ k • F k) := by
      ext i j
      rw [hAapply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
        smul_eq_mul, hAapply, hAapply]
      have hterm : ∀ k : Fin n, (a • x₁ + (1 - a) • x₂) k * F k i j
          = a * (x₁ k * F k i j) + (1 - a) * (x₂ k * F k i j) := by
        intro k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    show toE (G + ∑ k, (a • x₁ + (1 - a) • x₂) k • F k)
        = a • toE (G + ∑ k, x₁ k • F k) + (1 - a) • toE (G + ∑ k, x₂ k • F k)
    rw [hmat, toE_add, toE_smul, toE_smul]
  have hdisj : Disjoint (NDset nn) L := by
    rw [Set.disjoint_left]
    rintro y hy ⟨x, hx⟩
    refine hno x (Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_)
    · refine isHermitian_of_isSymm (isSymm_of_apply fun i j => ?_)
      simp only [Matrix.neg_apply]
      rw [isSymm_apply (hAsymm x) i j]
    · intro v hv
      have hq := hy v hv
      rw [← hx, ofE_toE] at hq
      rw [show (star v : Fin nn → ℝ) = v from star_trivial v, quad_neg]
      linarith
  obtain ⟨Φ, u, hΦC, hΦL⟩ :=
    geometric_hahn_banach_open (convex_NDset (nn := nn)) isOpen_NDset hLconv hdisj
  -- `M ↦ Φ (toE M)` is a linear functional on matrices.
  have hψ0 : Φ (toE (0 : Matrix (Fin nn) (Fin nn) ℝ)) = 0 := by
    rw [show toE (0 : Matrix (Fin nn) (Fin nn) ℝ) = 0 from by ext p; rfl, map_zero]
  have hψadd : ∀ M N : Matrix (Fin nn) (Fin nn) ℝ,
      Φ (toE (M + N)) = Φ (toE M) + Φ (toE N) := by
    intro M N; rw [toE_add, map_add]
  have hψsmul : ∀ (c : ℝ) (M : Matrix (Fin nn) (Fin nn) ℝ),
      Φ (toE (c • M)) = c * Φ (toE M) := by
    intro c M; rw [toE_smul, map_smul, smul_eq_mul]
  have hψneg : ∀ M : Matrix (Fin nn) (Fin nn) ℝ, Φ (toE (-M)) = -Φ (toE M) := by
    intro M; rw [toE_neg, map_neg]
  have hψsum : ∀ (s : Finset (Fin n)) (f : Fin n → Matrix (Fin nn) (Fin nn) ℝ),
      Φ (toE (∑ k ∈ s, f k)) = ∑ k ∈ s, Φ (toE (f k)) := by
    intro s f
    induction s using Finset.induction with
    | empty => simpa using hψ0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hψadd, ih]
  -- (a) `Φ` is nonpositive on negative definite matrices, because they form a cone.
  have hneg_le : ∀ M : Matrix (Fin nn) (Fin nn) ℝ,
      (∀ x : Fin nn → ℝ, x ≠ 0 → x ⬝ᵥ (M *ᵥ x) < 0) → Φ (toE M) ≤ 0 := by
    intro M hM
    by_contra hcon
    push_neg at hcon
    have hmemM : toE M ∈ NDset nn := by
      intro x hx; rw [ofE_toE]; exact hM x hx
    have htpos : 0 < (|u| + 1) / Φ (toE M) := div_pos (by positivity) hcon
    have hlt := hΦC _ (smul_mem_NDset htpos hmemM)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_gt hcon)] at hlt
    linarith [le_abs_self u]
  -- (b) The separating value is nonnegative.
  have hnegOne := negOne_mem_NDset (nn := nn) hnn
  have hnegOneval : Φ (toE (-1 : Matrix (Fin nn) (Fin nn) ℝ)) < u := hΦC _ hnegOne
  have hunn : 0 ≤ u := by
    by_contra hcon
    push_neg at hcon
    have hp : Φ (toE (-1 : Matrix (Fin nn) (Fin nn) ℝ)) < 0 := lt_trans hnegOneval hcon
    have hdiv : 0 < u / Φ (toE (-1 : Matrix (Fin nn) (Fin nn) ℝ)) := by
      rw [div_pos_iff]; right; exact ⟨hcon, hp⟩
    have h2 := hΦC _ (smul_mem_NDset hdiv hnegOne)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_lt hp)] at h2
    exact lt_irrefl u h2
  -- (c) `Φ` is nonnegative on positive semidefinite matrices, by a limiting argument.
  have hpsd_nonneg : ∀ N : Matrix (Fin nn) (Fin nn) ℝ,
      (∀ x : Fin nn → ℝ, 0 ≤ x ⬝ᵥ (N *ᵥ x)) → 0 ≤ Φ (toE N) := by
    intro N hN
    by_contra hcon
    push_neg at hcon
    set d : ℝ := -Φ (toE N) with hddef
    have hd : 0 < d := by rw [hddef]; linarith
    set K : ℝ := |Φ (toE (1 : Matrix (Fin nn) (Fin nn) ℝ))| with hKdef
    have hK : 0 ≤ K := abs_nonneg _
    have hψ1 : Φ (toE (1 : Matrix (Fin nn) (Fin nn) ℝ)) ≤ K := le_abs_self _
    have hKpos : (0 : ℝ) < K + 1 := by linarith
    have hεpos : 0 < d / (K + 1) := div_pos hd hKpos
    have hND : ∀ x : Fin nn → ℝ, x ≠ 0 →
        x ⬝ᵥ ((-(N + (d / (K + 1)) • (1 : Matrix (Fin nn) (Fin nn) ℝ))) *ᵥ x) < 0 := by
      intro x hx
      rw [quad_neg, quad_add, quad_smul_mat, quad_one]
      have h1 := hN x
      have h2 := mul_pos hεpos (dotProduct_self_pos hx)
      linarith
    have hle := hneg_le _ hND
    rw [hψneg, hψadd, hψsmul] at hle
    have hεK : (d / (K + 1)) * (K + 1) = d := div_mul_cancel₀ _ (ne_of_gt hKpos)
    have hnn0 : 0 ≤ (Φ (toE N) + (d / (K + 1)) * Φ (toE (1 : Matrix (Fin nn) (Fin nn) ℝ)))
        * (K + 1) := mul_nonneg (by linarith) hKpos.le
    have hexp : (Φ (toE N) + (d / (K + 1)) * Φ (toE (1 : Matrix (Fin nn) (Fin nn) ℝ))) * (K + 1)
        = -d * (K + 1) + d * Φ (toE (1 : Matrix (Fin nn) (Fin nn) ℝ)) := by
      have hN' : Φ (toE N) = -d := by rw [hddef]; ring
      calc (Φ (toE N) + (d / (K + 1)) * Φ (toE (1 : Matrix (Fin nn) (Fin nn) ℝ))) * (K + 1)
          = Φ (toE N) * (K + 1)
              + ((d / (K + 1)) * (K + 1)) * Φ (toE (1 : Matrix (Fin nn) (Fin nn) ℝ)) := by ring
        _ = -d * (K + 1) + d * Φ (toE (1 : Matrix (Fin nn) (Fin nn) ℝ)) := by rw [hεK, hN']
    rw [hexp] at hnn0
    have := mul_le_mul_of_nonneg_left hψ1 hd.le
    linarith
  -- Riesz representation of the separating functional, symmetrized.
  set w : EuclideanSpace ℝ (Fin nn × Fin nn) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin nn × Fin nn))).symm Φ with hwdef
  have hw : ∀ y, ⟪w, y⟫ = Φ y := by
    intro y; rw [hwdef, InnerProductSpace.toDual_symm_apply]
  set W : Matrix (Fin nn) (Fin nn) ℝ := ofE w with hWdef
  have hWE : toE W = w := by rw [hWdef, toE_ofE]
  have hψW : ∀ M : Matrix (Fin nn) (Fin nn) ℝ, Φ (toE M) = ∑ i, ∑ j, W i j * M i j := by
    intro M
    rw [← hw (toE M), ← hWE, inner_toE]
  set Z : Matrix (Fin nn) (Fin nn) ℝ := (2 : ℝ)⁻¹ • (W + Wᵀ) with hZdef
  have hZsymm : Z.IsSymm := by
    unfold Matrix.IsSymm
    rw [hZdef, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose,
      add_comm Wᵀ W]
  have hψZ : ∀ M : Matrix (Fin nn) (Fin nn) ℝ, M.IsSymm → Φ (toE M) = (M * Z).trace := by
    intro M hM
    have hswap : ∑ i, ∑ j, W j i * M i j = ∑ i, ∑ j, W i j * M i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [isSymm_apply hM i j]
    have hZij : ∀ i j, M i j * Z i j = (W i j * M i j + W j i * M i j) / 2 := by
      intro i j
      simp only [hZdef, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      ring
    have hinner : ∀ i : Fin nn, ∑ j, (W i j * M i j + W j i * M i j) / 2
        = ((∑ j, W i j * M i j) + (∑ j, W j i * M i j)) / 2 := by
      intro i; rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [trace_mul_eq_sum M Z hZsymm, hψW M,
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hZij i j,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i,
      ← Finset.sum_div, Finset.sum_add_distrib, hswap]
    ring
  -- The certificate.
  have hZpsd : Z.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_isSymm hZsymm) ?_
    intro v
    rw [show (star v : Fin nn → ℝ) = v from star_trivial v]
    have hq : v ⬝ᵥ (Z *ᵥ v) = (Matrix.vecMulVec v v * Z).trace := by
      rw [trace_mul_eq_sum _ Z hZsymm, quad_eq_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        simp [Matrix.vecMulVec_apply]; ring
    rw [hq, ← hψZ _ (vecMulVec_isSymm v)]
    exact hpsd_nonneg _ fun x => by rw [quad_vecMulVec]; positivity
  have hlinear : ∀ y : Fin n → ℝ,
      Φ (toE (G + ∑ k, y k • F k)) = Φ (toE G) + ∑ k, y k * Φ (toE (F k)) := by
    intro y
    rw [hψadd, hψsum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hψsmul (y k) (F k)
  have hLbound : ∀ y : Fin n → ℝ, u ≤ Φ (toE G) + ∑ k, y k * Φ (toE (F k)) := by
    intro y; rw [← hlinear y]; exact hΦL _ ⟨y, rfl⟩
  have hGval : u ≤ Φ (toE G) := by
    have h := hLbound 0
    have hz : ∑ k, (0 : Fin n → ℝ) k * Φ (toE (F k)) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp
    rw [hz, add_zero] at h
    exact h
  have hnegOneSymm : (-1 : Matrix (Fin nn) (Fin nn) ℝ).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_neg, Matrix.transpose_one]
  have hZne : Z ≠ 0 := by
    intro hz
    have h1 : Φ (toE (-1 : Matrix (Fin nn) (Fin nn) ℝ)) = 0 := by
      rw [hψZ _ hnegOneSymm, hz, Matrix.mul_zero, Matrix.trace_zero]
    have h2 : Φ (toE G) = 0 := by rw [hψZ _ hG, hz, Matrix.mul_zero, Matrix.trace_zero]
    rw [h1] at hnegOneval
    rw [h2] at hGval
    linarith
  refine ⟨Z, hZpsd, hZne, fun i => ?_, ?_⟩
  · -- `tr (Fᵢ Z) = 0`, because the affine family is unbounded in each direction.
    rw [← hψZ _ (hF i)]
    by_contra hci
    have hsel : ∀ t : ℝ, ∑ k, (fun k => if k = i then t else 0) k * Φ (toE (F k))
        = t * Φ (toE (F i)) := by
      intro t
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hval := hLbound (fun k => if k = i then (u - 1 - Φ (toE G)) / Φ (toE (F i)) else 0)
    rw [hsel, div_mul_cancel₀ _ hci] at hval
    linarith
  · rw [← hψZ _ hG]; linarith

/-! ### Main theorem -/

end LMIAux

open LMIAux in
theorem solution {n nn : ℕ}
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm) :
    (∃ x : Fin n → ℝ, (-(G + ∑ i, x i • F i)).PosDef) ↔
      ¬∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧
        (∀ i, ((F i) * Z).trace = 0) ∧ 0 ≤ (G * Z).trace := by
  classical
  constructor
  · -- Both alternatives cannot hold: `tr(PZ) > 0` while the constraints force `tr(PZ) ≤ 0`.
    rintro ⟨x, hx⟩ ⟨Z, hZ, hZne, hFZ, hGZ⟩
    have hpos := trace_mul_pos _ Z hx hZ hZne
    have hexpand : ((-(G + ∑ i, x i • F i)) * Z).trace
        = -((G * Z).trace) - ∑ i, x i * ((F i * Z).trace) := by
      rw [Matrix.neg_mul, Matrix.trace_neg, Matrix.add_mul, Matrix.trace_add,
        Finset.sum_mul, Matrix.trace_sum]
      have : ∀ i, ((x i • F i) * Z).trace = x i * ((F i * Z).trace) := by
        intro i; rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [Finset.sum_congr rfl fun i _ => this i]
      ring
    rw [hexpand] at hpos
    have hzero : ∑ i, x i * ((F i * Z).trace) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hFZ i, mul_zero]
    rw [hzero] at hpos
    linarith
  · -- Otherwise the separating hyperplane produces the certificate.
    intro hnoZ
    by_contra hno
    push_neg at hno
    rcases Nat.eq_zero_or_pos nn with h0 | hpos
    · subst h0
      exact hno 0 (Matrix.PosDef.of_dotProduct_mulVec_pos
        (isHermitian_of_isSymm (isSymm_of_apply fun i _ => Fin.elim0 i))
        (fun v hv => absurd (funext fun i => Fin.elim0 i) hv))
    · exact hnoZ (separation hpos F hF G hG hno)
