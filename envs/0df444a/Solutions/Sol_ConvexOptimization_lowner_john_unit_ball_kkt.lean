-- Prove2me | solution 1 for ConvexOptimization.lowner_john_unit_ball_kkt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T17:04:20.487407+00:00
-- url     : https://prove2.me/submissions/dd31a2b8-8ffc-4227-9ab8-d7bbb1e97a2f

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open Matrix Unitary
open ConvexOptimization

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace LJKAux

variable {nn : ℕ}

/-! ### Symmetry, entrywise -/

theorem isSymm_apply {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) (i j : Fin nn) :
    M j i = M i j := congrFun (congrFun h i) j

theorem isHermitian_of_isSymm {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) :
    M.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact h

/-! ### Elementary dot-product algebra -/

theorem dotProduct_self_nonneg (v : Fin nn → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem dotProduct_self_pos {v : Fin nn → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  rw [dotProduct]
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr (by simpa using hi)

theorem dot_add_smul (u z : Fin nn → ℝ) (t : ℝ) :
    (u + t • z) ⬝ᵥ (u + t • z) = u ⬝ᵥ u + 2 * t * (u ⬝ᵥ z) + t ^ 2 * (z ⬝ᵥ z) := by
  simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem smul_mulVec (c : ℝ) (A : Matrix (Fin nn) (Fin nn) ℝ) (v : Fin nn → ℝ) :
    (c • A) *ᵥ v = c • (A *ᵥ v) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sq_le_dot (v : Fin nn → ℝ) (j : Fin nn) : v j * v j ≤ v ⬝ᵥ v :=
  Finset.single_le_sum (f := fun k => v k * v k) (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)

theorem abs_mul_le_dot (v : Fin nn → ℝ) (j k : Fin nn) : |v j| * |v k| ≤ v ⬝ᵥ v := by
  have h1 := sq_le_dot v j
  have h2 := sq_le_dot v k
  have haj := abs_mul_abs_self (v j)
  have hak := abs_mul_abs_self (v k)
  nlinarith [sq_nonneg (|v j| - |v k|), abs_nonneg (v j), abs_nonneg (v k)]

theorem quad_eq_sum (M : Matrix (Fin nn) (Fin nn) ℝ) (v : Fin nn → ℝ) :
    v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, M i j * (v i * v j) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A crude but sufficient operator bound: the quadratic form of `S` is controlled by the
sum of the absolute values of its entries. -/
theorem quad_abs_le (S : Matrix (Fin nn) (Fin nn) ℝ) (v : Fin nn → ℝ) :
    |v ⬝ᵥ (S *ᵥ v)| ≤ (∑ j, ∑ k, |S j k|) * (v ⬝ᵥ v) := by
  have hb : (∑ j, ∑ k, |S j k|) * (v ⬝ᵥ v) = ∑ j, ∑ k, |S j k| * (v ⬝ᵥ v) := by
    simp only [Finset.sum_mul]
  rw [quad_eq_sum, hb]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hrw : |S j k * (v j * v k)| = |S j k| * (|v j| * |v k|) := by
    rw [abs_mul, abs_mul]
  rw [hrw]
  exact mul_le_mul_of_nonneg_left (abs_mul_le_dot v j k) (abs_nonneg _)

/-- Symmetrising a matrix does not change its quadratic form. -/
theorem quad_symmetrize (W : Matrix (Fin nn) (Fin nn) ℝ) (v : Fin nn → ℝ) :
    v ⬝ᵥ (((2 : ℝ)⁻¹ • (W + Wᵀ)) *ᵥ v) = v ⬝ᵥ (W *ᵥ v) := by
  have hswap : ∑ i, ∑ j, (Wᵀ) i j * (v i * v j) = ∑ i, ∑ j, W i j * (v i * v j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      simp only [Matrix.transpose_apply]; ring
  rw [quad_eq_sum, quad_eq_sum]
  calc ∑ i, ∑ j, ((2 : ℝ)⁻¹ • (W + Wᵀ)) i j * (v i * v j)
      = ∑ i, ((2 : ℝ)⁻¹ * ∑ j, W i j * (v i * v j)
          + (2 : ℝ)⁻¹ * ∑ j, (Wᵀ) i j * (v i * v j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
        ring
    _ = (2 : ℝ)⁻¹ * (∑ i, ∑ j, W i j * (v i * v j))
          + (2 : ℝ)⁻¹ * (∑ i, ∑ j, (Wᵀ) i j * (v i * v j)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = ∑ i, ∑ j, W i j * (v i * v j) := by rw [hswap]; ring

/-! ### Identifying matrices and vectors with Euclidean spaces -/

/-- Coordinatewise identification of `nn × nn` matrices with a Euclidean space. -/
noncomputable def toE (M : Matrix (Fin nn) (Fin nn) ℝ) :
    EuclideanSpace ℝ (Fin nn × Fin nn) := WithLp.toLp 2 (fun p => M p.1 p.2)

/-- The inverse identification. -/
def ofE (y : EuclideanSpace ℝ (Fin nn × Fin nn)) : Matrix (Fin nn) (Fin nn) ℝ :=
  Matrix.of fun i j => y (i, j)

@[simp] theorem ofE_toE (M : Matrix (Fin nn) (Fin nn) ℝ) : ofE (toE M) = M := rfl

@[simp] theorem toE_ofE (y : EuclideanSpace ℝ (Fin nn × Fin nn)) : toE (ofE y) = y := by
  ext p; rfl

theorem toE_inj : Function.Injective (toE (nn := nn)) :=
  Function.LeftInverse.injective ofE_toE

theorem toE_add (M N : Matrix (Fin nn) (Fin nn) ℝ) : toE (M + N) = toE M + toE N := by
  ext p; rfl

theorem toE_smul (c : ℝ) (M : Matrix (Fin nn) (Fin nn) ℝ) : toE (c • M) = c • toE M := by
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

theorem inner_toE_one (M : Matrix (Fin nn) (Fin nn) ℝ) :
    ⟪toE M, toE (1 : Matrix (Fin nn) (Fin nn) ℝ)⟫ = M.trace := by
  rw [inner_toE]
  simp [Matrix.one_apply, Matrix.trace, Matrix.diag_apply]

theorem inner_toE_vecMulVec (M : Matrix (Fin nn) (Fin nn) ℝ) (v : Fin nn → ℝ) :
    ⟪toE M, toE (Matrix.vecMulVec v v)⟫ = v ⬝ᵥ (M *ᵥ v) := by
  rw [inner_toE, quad_eq_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl

/-- Coordinatewise identification of vectors with a Euclidean space. -/
noncomputable def toV (v : Fin nn → ℝ) : EuclideanSpace ℝ (Fin nn) := WithLp.toLp 2 v

/-- The inverse identification. -/
def ofV (y : EuclideanSpace ℝ (Fin nn)) : Fin nn → ℝ := fun i => y i

@[simp] theorem ofV_toV (v : Fin nn → ℝ) : ofV (toV v) = v := rfl

@[simp] theorem toV_ofV (y : EuclideanSpace ℝ (Fin nn)) : toV (ofV y) = y := by
  ext i; rfl

theorem toV_inj : Function.Injective (toV (nn := nn)) :=
  Function.LeftInverse.injective ofV_toV

theorem toV_add (u v : Fin nn → ℝ) : toV (u + v) = toV u + toV v := by ext i; rfl

theorem toV_smul (c : ℝ) (v : Fin nn → ℝ) : toV (c • v) = c • toV v := by ext i; rfl

theorem toV_zero : toV (0 : Fin nn → ℝ) = 0 := by ext i; rfl

theorem toV_sum {ι : Type*} (s : Finset ι) (f : ι → Fin nn → ℝ) :
    toV (∑ i ∈ s, f i) = ∑ i ∈ s, toV (f i) := by
  classical
  induction s using Finset.induction with
  | empty => ext p; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toV_add, ih]

theorem inner_toV (u v : Fin nn → ℝ) : ⟪toV u, toV v⟫ = u ⬝ᵥ v := by
  rw [PiLp.inner_apply, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by simp [toV, mul_comm]

/-! ### `det (1 + ε S) > 1` for small `ε > 0`, when `tr S > 0` -/

theorem det_conj (U : Matrix.unitaryGroup (Fin nn) ℝ) (X : Matrix (Fin nn) (Fin nn) ℝ) :
    (conjStarAlgAut ℝ (Matrix (Fin nn) (Fin nn) ℝ) U X).det = X.det := by
  have h : (U : Matrix (Fin nn) (Fin nn) ℝ) * star (U : Matrix (Fin nn) (Fin nn) ℝ) = 1 := U.2.2
  have hd : (U : Matrix (Fin nn) (Fin nn) ℝ).det
      * (star (U : Matrix (Fin nn) (Fin nn) ℝ)).det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  simp only [conjStarAlgAut_apply, Matrix.det_mul]
  linear_combination X.det * hd

/-- A quantitative lower bound for `log (1 + t)`, valid on `t ≥ -1/2`. -/
theorem log_lb (t : ℝ) (ht : -(2 : ℝ)⁻¹ ≤ t) : t - 2 * t ^ 2 ≤ Real.log (1 + t) := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : 1 - (1 + t)⁻¹ ≤ Real.log (1 + t) := Real.one_sub_inv_le_log_of_pos h1
  have key : (1 - (1 + t)⁻¹) - (t - 2 * t ^ 2) = (t ^ 2 * (1 + 2 * t)) / (1 + t) := by
    field_simp
    ring
  have hnn : 0 ≤ (t ^ 2 * (1 + 2 * t)) / (1 + t) :=
    div_nonneg (mul_nonneg (sq_nonneg t) (by linarith)) h1.le
  linarith

/-- **The determinant increases in the direction of any symmetric matrix of positive trace.**
This is the first-order optimality computation behind B&V (8.11): `d/dε det (I + εS) = tr S`. -/
theorem det_perturb (S : Matrix (Fin nn) (Fin nn) ℝ) (hS : S.IsHermitian) (htr : 0 < S.trace) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      1 < ((1 : Matrix (Fin nn) (Fin nn) ℝ) + ε • S).det := by
  classical
  set d : Fin nn → ℝ := hS.eigenvalues with hd
  have htrace : S.trace = ∑ i, d i := by simpa using hS.trace_eq_sum_eigenvalues
  -- the determinant, diagonalised
  have hdetid : ∀ ε : ℝ, ((1 : Matrix (Fin nn) (Fin nn) ℝ) + ε • S).det
      = ∏ i, (1 + ε * d i) := by
    intro ε
    set U := hS.eigenvectorUnitary with hU
    set D : Matrix (Fin nn) (Fin nn) ℝ := Matrix.diagonal (RCLike.ofReal ∘ d) with hD
    have hspec : S = conjStarAlgAut ℝ (Matrix (Fin nn) (Fin nn) ℝ) U D := hS.spectral_theorem
    have hkey : (1 : Matrix (Fin nn) (Fin nn) ℝ) + ε • S
        = conjStarAlgAut ℝ (Matrix (Fin nn) (Fin nn) ℝ) U (1 + ε • D) := by
      rw [map_add, map_one, map_smul, ← hspec]
    have hDeq : (1 : Matrix (Fin nn) (Fin nn) ℝ) + ε • D
        = Matrix.diagonal (fun i => 1 + ε * d i) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [hD]
      · simp [hD, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]
    rw [hkey, det_conj, hDeq, Matrix.det_diagonal]
  set T : ℝ := ∑ i, d i with hT
  have hTpos : 0 < T := by rw [htrace] at htr; exact htr
  set Q : ℝ := ∑ i, (d i) ^ 2 with hQ
  have hQnn : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQpos : 0 < Q := by
    rcases hQnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hall : ∀ i, d i = 0 := by
        intro i
        have hz := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ Finset.univ) => sq_nonneg (d j))).mp h.symm i (Finset.mem_univ i)
        exact pow_eq_zero_iff (two_ne_zero) |>.mp hz
      rw [hT] at hTpos
      simp only [hall, Finset.sum_const_zero] at hTpos
      exact lt_irrefl 0 hTpos
  have hdQ : ∀ i, (d i) ^ 2 ≤ Q :=
    fun i => Finset.single_le_sum (f := fun j => (d j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  set BB : ℝ := 1 + Q with hBB
  have hBBpos : 0 < BB := by rw [hBB]; linarith
  have hdB : ∀ i, |d i| ≤ BB := by
    intro i
    rcases le_or_gt |d i| 1 with h | h
    · rw [hBB]; linarith
    · have h1 : |d i| * |d i| = (d i) ^ 2 := by rw [abs_mul_abs_self]; ring
      have := hdQ i
      rw [hBB]
      nlinarith [abs_nonneg (d i)]
  refine ⟨min (1 / (2 * BB)) (T / (4 * Q)), lt_min (by positivity) (by positivity), ?_⟩
  intro ε hεpos hεle
  have hε1 : ε ≤ 1 / (2 * BB) := hεle.trans (min_le_left _ _)
  have hε2 : ε ≤ T / (4 * Q) := hεle.trans (min_le_right _ _)
  have hεB : ε * BB ≤ 1 / 2 := by
    have h := (le_div_iff₀ (show (0:ℝ) < 2 * BB by positivity)).mp hε1
    linarith
  have hbd : ∀ i, |ε * d i| ≤ 1 / 2 := by
    intro i
    rw [abs_mul, abs_of_pos hεpos]
    calc ε * |d i| ≤ ε * BB := mul_le_mul_of_nonneg_left (hdB i) hεpos.le
      _ ≤ 1 / 2 := hεB
  have hfacpos : ∀ i, 0 < 1 + ε * d i := by
    intro i
    have := (abs_le.mp (hbd i)).1
    linarith
  have hprodpos : 0 < ∏ i, (1 + ε * d i) := Finset.prod_pos fun i _ => hfacpos i
  have hlogeq : Real.log (∏ i, (1 + ε * d i)) = ∑ i, Real.log (1 + ε * d i) :=
    Real.log_prod (fun i _ => (hfacpos i).ne')
  have hlb : ∀ i, (ε * d i) - 2 * (ε * d i) ^ 2 ≤ Real.log (1 + ε * d i) := by
    intro i
    exact log_lb _ (by linarith [(abs_le.mp (hbd i)).1])
  have hsplit : ∑ i, ((ε * d i) - 2 * (ε * d i) ^ 2) = ε * T - 2 * ε ^ 2 * Q := by
    rw [hT, hQ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcore : 0 < ε * T - 2 * ε ^ 2 * Q := by
    have h4 : ε * (4 * Q) ≤ T := (le_div_iff₀ (show (0:ℝ) < 4 * Q by positivity)).mp hε2
    nlinarith [mul_pos hεpos hQpos]
  have hlogpos : 0 < Real.log (∏ i, (1 + ε * d i)) := by
    rw [hlogeq]
    calc (0:ℝ) < ε * T - 2 * ε ^ 2 * Q := hcore
      _ = ∑ i, ((ε * d i) - 2 * (ε * d i) ^ 2) := hsplit.symm
      _ ≤ ∑ i, Real.log (1 + ε * d i) := Finset.sum_le_sum fun i _ => hlb i
  rw [hdetid ε]
  exact (Real.log_pos_iff hprodpos.le).mp hlogpos

/-! ### No improving perturbation direction can exist -/

/-- **First-order optimality of the Löwner–John ellipsoid, contrapositive form.**
If the unit ball is optimal for the points `x i`, there is no symmetric `S` with positive
trace and no vector `c` making the perturbation `A = I + εS`, `b = εc` strictly feasible at
every active point.  Perturbing by such a direction would enlarge `det A` while keeping all
the points inside the ellipsoid. -/
theorem no_improving_direction {nn m : ℕ} (x : Fin m → Fin nn → ℝ)
    (hball : ∀ i, x i ⬝ᵥ x i ≤ 1)
    (hmax : ∀ (A' : Matrix (Fin nn) (Fin nn) ℝ) (b' : Fin nn → ℝ),
      A'.IsSymm → A'.PosDef → Set.range x ⊆ ellipsoidBody A' b' →
      A'.det ≤ (1 : Matrix (Fin nn) (Fin nn) ℝ).det)
    (S : Matrix (Fin nn) (Fin nn) ℝ) (hSsymm : S.IsSymm) (c : Fin nn → ℝ)
    (htr : 0 < S.trace)
    (hact : ∀ i, x i ⬝ᵥ x i = 1 → (x i) ⬝ᵥ (S *ᵥ (x i)) + (x i) ⬝ᵥ c < 0) : False := by
  classical
  obtain ⟨ε₀, hε₀pos, hdet⟩ := det_perturb S (isHermitian_of_isSymm hSsymm) htr
  set g : Fin m → ℝ := fun i => (x i) ⬝ᵥ (S *ᵥ (x i)) + (x i) ⬝ᵥ c with hg
  set hq : Fin m → ℝ := fun i => (S *ᵥ x i + c) ⬝ᵥ (S *ᵥ x i + c) with hqdef
  have hqnn : ∀ i, 0 ≤ hq i := fun i => dotProduct_self_nonneg _
  -- a uniform positive slack `eta0`
  set eta : Fin m → ℝ :=
    fun i => if x i ⬝ᵥ x i = 1 then -(g i) else 1 - x i ⬝ᵥ x i with hetadef
  have hetapos : ∀ i, 0 < eta i := by
    intro i
    by_cases h : x i ⬝ᵥ x i = 1
    · simp only [hetadef, if_pos h]
      linarith [hact i h]
    · simp only [hetadef, if_neg h]
      have := lt_of_le_of_ne (hball i) h
      linarith
  set eta0 : ℝ := ∏ i, min (eta i) 1 with heta0
  have hminpos : ∀ i, 0 < min (eta i) 1 := fun i => lt_min (hetapos i) one_pos
  have heta0pos : 0 < eta0 := Finset.prod_pos fun i _ => hminpos i
  have heta0le : ∀ j, eta0 ≤ eta j := by
    intro j
    have hrest : ∏ i ∈ Finset.univ.erase j, min (eta i) 1 ≤ 1 :=
      Finset.prod_le_one (fun i _ => (hminpos i).le) (fun i _ => min_le_right _ _)
    have hsp : eta0 = (∏ i ∈ Finset.univ.erase j, min (eta i) 1) * min (eta j) 1 := by
      rw [heta0]
      exact (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
    calc eta0 = (∏ i ∈ Finset.univ.erase j, min (eta i) 1) * min (eta j) 1 := hsp
      _ ≤ 1 * min (eta j) 1 := mul_le_mul_of_nonneg_right hrest (hminpos j).le
      _ = min (eta j) 1 := one_mul _
      _ ≤ eta j := min_le_left _ _
  -- a uniform bound `BB` on the first- and second-order coefficients
  set BB : ℝ := 1 + ∑ i, (|g i| + hq i) with hBB
  have hBBge : 1 ≤ BB := by
    have : 0 ≤ ∑ i, (|g i| + hq i) :=
      Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (hqnn i)
    rw [hBB]; linarith
  have hgB : ∀ i, |g i| ≤ BB := by
    intro i
    have h1 : |g i| + hq i ≤ ∑ j, (|g j| + hq j) :=
      Finset.single_le_sum (f := fun j => |g j| + hq j)
        (fun j _ => add_nonneg (abs_nonneg _) (hqnn j)) (Finset.mem_univ i)
    have := hqnn i
    rw [hBB]; linarith
  have hqB : ∀ i, hq i ≤ BB := by
    intro i
    have h1 : |g i| + hq i ≤ ∑ j, (|g j| + hq j) :=
      Finset.single_le_sum (f := fun j => |g j| + hq j)
        (fun j _ => add_nonneg (abs_nonneg _) (hqnn j)) (Finset.mem_univ i)
    have := abs_nonneg (g i)
    rw [hBB]; linarith
  -- a uniform bound `CC` keeping `1 + εS` positive definite
  set C0 : ℝ := ∑ j, ∑ k, |S j k| with hC0
  have hC0nn : 0 ≤ C0 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  set CC : ℝ := 1 + C0 with hCC
  have hCCpos : 0 < CC := by rw [hCC]; linarith
  -- the step size
  set eps : ℝ := min (min ε₀ 1) (min (eta0 / (4 * BB)) (1 / (2 * CC))) with heps
  have hBBpos : 0 < BB := by linarith
  have hepspos : 0 < eps := by
    refine lt_min (lt_min hε₀pos one_pos) (lt_min ?_ ?_)
    · exact div_pos heta0pos (by linarith)
    · exact div_pos one_pos (by linarith)
  have heps1 : eps ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hepsε₀ : eps ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hepsB : eps ≤ eta0 / (4 * BB) := (min_le_right _ _).trans (min_le_left _ _)
  have hepsC : eps ≤ 1 / (2 * CC) := (min_le_right _ _).trans (min_le_right _ _)
  have h4B : eps * (4 * BB) ≤ eta0 := (le_div_iff₀ (by linarith)).mp hepsB
  have hepsBB : eps * BB ≤ eta0 / 4 := by linarith
  have hepsC0 : eps * C0 ≤ 1 / 2 := by
    have h := (le_div_iff₀ (show (0:ℝ) < 2 * CC by linarith)).mp hepsC
    nlinarith [hepspos, hC0nn]
  -- the perturbed ellipsoid
  set A' : Matrix (Fin nn) (Fin nn) ℝ := 1 + eps • S with hA'
  have hA'symm : A'.IsSymm := by
    rw [hA', Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      hSsymm]
  have hA'pd : A'.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_of_isSymm hA'symm) ?_
    intro v hv
    have hstar : star v = v := by funext k; simp
    rw [hstar]
    have hvv : 0 < v ⬝ᵥ v := dotProduct_self_pos hv
    have hexp : v ⬝ᵥ (A' *ᵥ v) = v ⬝ᵥ v + eps * (v ⬝ᵥ (S *ᵥ v)) := by
      rw [hA', Matrix.add_mulVec, Matrix.one_mulVec, smul_mulVec, dotProduct_add,
        dotProduct_smul]
      ring
    have hb := quad_abs_le S v
    rw [← hC0] at hb
    have hb2 := abs_le.mp hb
    rw [hexp]
    nlinarith [hb2.1, hb2.2, hepspos, hvv, hepsC0]
  have hcov : Set.range x ⊆ ellipsoidBody A' (eps • c) := by
    rintro _ ⟨i, rfl⟩
    show (A' *ᵥ x i + eps • c) ⬝ᵥ (A' *ᵥ x i + eps • c) ≤ 1
    have hvec : A' *ᵥ x i + eps • c = x i + eps • (S *ᵥ x i + c) := by
      rw [hA', Matrix.add_mulVec, Matrix.one_mulVec, smul_mulVec, smul_add]
      abel
    have hgi : x i ⬝ᵥ (S *ᵥ x i + c) = g i := by rw [dotProduct_add]
    have hqi : (S *ᵥ x i + c) ⬝ᵥ (S *ᵥ x i + c) = hq i := rfl
    rw [hvec, dot_add_smul, hgi, hqi]
    have t2a : eps * hq i ≤ eps * BB := mul_le_mul_of_nonneg_left (hqB i) hepspos.le
    have t2 : eps ^ 2 * hq i ≤ eps * (eta0 / 4) := by
      have := mul_le_mul_of_nonneg_left (t2a.trans hepsBB) hepspos.le
      nlinarith
    by_cases h : x i ⬝ᵥ x i = 1
    · have hgle : g i ≤ -eta0 := by
        have := heta0le i
        simp only [hetadef, if_pos h] at this
        linarith
      rw [h]
      nlinarith [hepspos, heta0pos]
    · have hqle : x i ⬝ᵥ x i ≤ 1 - eta0 := by
        have := heta0le i
        simp only [hetadef, if_neg h] at this
        linarith
      have t1 : 2 * eps * g i ≤ eta0 / 2 := by
        have h1 : g i ≤ |g i| := le_abs_self _
        have h2 : |g i| ≤ BB := hgB i
        nlinarith [hepspos, hepsBB]
      have t3 : eps * (eta0 / 4) ≤ eta0 / 4 := by nlinarith [heta0pos, heps1, hepspos]
      linarith
  have hfinal := hmax A' (eps • c) hA'symm hA'pd hcov
  rw [Matrix.det_one] at hfinal
  have hd2 := hdet eps hepspos hepsε₀
  rw [← hA'] at hd2
  linarith

end LJKAux

open LJKAux in
/-- **KKT conditions for the Löwner–John ellipsoid of a finite point set** (B&V §8.4.1).
If the *unit ball* is the minimum-volume ellipsoid covering `x 1, …, x m`, then there are
multipliers `λ i ≥ 0`, supported on the points that touch the boundary, with
`∑ λ i x i x iᵀ = I`, `∑ λ i x i = 0` and `∑ λ i = n`.  These are exactly equations
(8.11) of Boyd–Vandenberghe. -/
theorem solution {nn m : ℕ} (x : Fin m → Fin nn → ℝ)
    (hopt : IsLownerJohn (1 : Matrix (Fin nn) (Fin nn) ℝ) 0 (Set.range x)) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧
      (∑ i, lam i • Matrix.vecMulVec (x i) (x i)) = (1 : Matrix (Fin nn) (Fin nn) ℝ) ∧
      (∑ i, lam i • x i) = 0 ∧
      (∀ i, lam i * (1 - x i ⬝ᵥ x i) = 0) ∧
      (∑ i, lam i) = (nn : ℝ) := by
  classical
  obtain ⟨-, -, hcover, hmax⟩ := hopt
  have hball : ∀ i, x i ⬝ᵥ x i ≤ 1 := by
    intro i
    have h := hcover (Set.mem_range_self i)
    simpa [ellipsoidBody, Matrix.one_mulVec] using h
  rcases Nat.eq_zero_or_pos nn with hnn0 | hnnpos
  · subst hnn0
    refine ⟨fun _ => 0, fun i => le_refl 0, ?_, ?_, fun i => by ring, ?_⟩
    · ext i j; exact absurd i.isLt (by omega)
    · funext i; exact absurd i.isLt (by omega)
    · simp
  have hnnR : (0 : ℝ) < (nn : ℝ) := by exact_mod_cast hnnpos
  -- The KKT system, phrased as membership of a convex hull in `Sym × ℝⁿ`.
  set u : Fin m → (EuclideanSpace ℝ (Fin nn × Fin nn) × EuclideanSpace ℝ (Fin nn)) :=
    fun i => (toE (Matrix.vecMulVec (x i) (x i)), toV (x i)) with hu
  set w : (EuclideanSpace ℝ (Fin nn × Fin nn) × EuclideanSpace ℝ (Fin nn)) :=
    ((nn : ℝ)⁻¹ • toE (1 : Matrix (Fin nn) (Fin nn) ℝ), 0) with hw
  set U : Set (EuclideanSpace ℝ (Fin nn × Fin nn) × EuclideanSpace ℝ (Fin nn)) :=
    u '' {i | x i ⬝ᵥ x i = 1} with hU
  have hUfin : U.Finite := Set.Finite.image _ (Set.toFinite _)
  set C : Set (EuclideanSpace ℝ (Fin nn × Fin nn) × EuclideanSpace ℝ (Fin nn)) :=
    {y | ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, x i ⬝ᵥ x i ≠ 1 → lam i = 0) ∧
      (∑ i, lam i) = 1 ∧ y = ∑ i, lam i • u i} with hC
  have hUC : U ⊆ C := by
    rintro p ⟨i₀, hi₀, rfl⟩
    refine ⟨fun i => if i = i₀ then (1 : ℝ) else 0, ?_, ?_, ?_, ?_⟩
    · intro i; by_cases h : i = i₀ <;> simp [h]
    · intro i hi
      by_cases h : i = i₀
      · subst h; exact absurd hi₀ hi
      · simp [h]
    · simp
    · simp
  have hCconv : Convex ℝ C := by
    rintro y₁ ⟨l₁, h₁n, h₁s, h₁t, rfl⟩ y₂ ⟨l₂, h₂n, h₂s, h₂t, rfl⟩ a b ha hb hab
    refine ⟨fun i => a * l₁ i + b * l₂ i, ?_, ?_, ?_, ?_⟩
    · exact fun i => add_nonneg (mul_nonneg ha (h₁n i)) (mul_nonneg hb (h₂n i))
    · intro i hi
      show a * l₁ i + b * l₂ i = 0
      rw [h₁s i hi, h₂s i hi]; ring
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₁t, h₂t]
      linarith
    · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [add_smul, smul_smul, smul_smul]
  by_cases hmem : w ∈ convexHull ℝ U
  · -- the multipliers exist; rescale by `n`
    obtain ⟨lam, hlnn, hlsupp, hlsum, hleq⟩ := convexHull_min hUC hCconv hmem
    have hfst := congrArg (LinearMap.fst ℝ (EuclideanSpace ℝ (Fin nn × Fin nn))
      (EuclideanSpace ℝ (Fin nn))) hleq
    have hsnd := congrArg (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin nn × Fin nn))
      (EuclideanSpace ℝ (Fin nn))) hleq
    rw [map_sum] at hfst hsnd
    simp only [map_smul, LinearMap.fst_apply, LinearMap.snd_apply, hw, hu] at hfst hsnd
    refine ⟨fun i => (nn : ℝ) * lam i, fun i => mul_nonneg hnnR.le (hlnn i), ?_, ?_, ?_, ?_⟩
    · refine toE_inj ?_
      rw [toE_sum]
      have hstep : ∀ i, toE (((nn : ℝ) * lam i) • Matrix.vecMulVec (x i) (x i))
          = (nn : ℝ) • (lam i • toE (Matrix.vecMulVec (x i) (x i))) := by
        intro i; rw [toE_smul, mul_smul]
      rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.smul_sum, ← hfst,
        smul_smul, mul_inv_cancel₀ (ne_of_gt hnnR), one_smul]
    · refine toV_inj ?_
      rw [toV_sum, toV_zero]
      have hstep : ∀ i, toV (((nn : ℝ) * lam i) • x i) = (nn : ℝ) • (lam i • toV (x i)) := by
        intro i; rw [toV_smul, mul_smul]
      rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.smul_sum, ← hsnd, smul_zero]
    · intro i
      show ((nn : ℝ) * lam i) * (1 - x i ⬝ᵥ x i) = 0
      by_cases h : x i ⬝ᵥ x i = 1
      · rw [h]; ring
      · rw [hlsupp i h]; ring
    · rw [← Finset.mul_sum, hlsum, mul_one]
  · -- otherwise a separating hyperplane gives an improving perturbation direction
    exfalso
    obtain ⟨f, α, hlt, hgt⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ U) (hUfin.isClosed_convexHull ℝ) hmem
    set g₁ : EuclideanSpace ℝ (Fin nn × Fin nn) →L[ℝ] ℝ :=
      f.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin nn × Fin nn))
        (EuclideanSpace ℝ (Fin nn))) with hg₁
    set g₂ : EuclideanSpace ℝ (Fin nn) →L[ℝ] ℝ :=
      f.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin nn × Fin nn))
        (EuclideanSpace ℝ (Fin nn))) with hg₂
    have hsplit : ∀ (a : EuclideanSpace ℝ (Fin nn × Fin nn)) (b : EuclideanSpace ℝ (Fin nn)),
        f (a, b) = g₁ a + g₂ b := by
      intro a b
      have h1 : ((a, b) : EuclideanSpace ℝ (Fin nn × Fin nn) × EuclideanSpace ℝ (Fin nn))
          = (a, 0) + (0, b) := by simp
      rw [h1, map_add]
      rfl
    set z₁ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin nn × Fin nn))).symm g₁ with hz₁d
    set z₂ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin nn))).symm g₂ with hz₂d
    have hz₁ : ∀ a, ⟪z₁, a⟫ = g₁ a := fun a => InnerProductSpace.toDual_symm_apply
    have hz₂ : ∀ b, ⟪z₂, b⟫ = g₂ b := fun b => InnerProductSpace.toDual_symm_apply
    set W : Matrix (Fin nn) (Fin nn) ℝ := ofE z₁ with hW
    set cc : Fin nn → ℝ := ofV z₂ with hcc
    have hWz : toE W = z₁ := by rw [hW, toE_ofE]
    have hccz : toV cc = z₂ := by rw [hcc, toV_ofV]
    set S : Matrix (Fin nn) (Fin nn) ℝ :=
      (2 : ℝ)⁻¹ • (W + Wᵀ) - α • (1 : Matrix (Fin nn) (Fin nn) ℝ) with hS
    -- `S` is symmetric
    have hSsymm : S.IsSymm := by
      rw [hS, Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul,
        Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_one, add_comm Wᵀ W]
    -- the value of `f` at `w` is `(tr W)/n`
    have hfw : f w = (nn : ℝ)⁻¹ * W.trace := by
      rw [hw, hsplit, map_smul, map_zero, add_zero, ← hz₁, ← hWz, inner_toE_one]
      rfl
    -- the value of `f` at an active point
    have hfu : ∀ i, f (u i) = (x i) ⬝ᵥ (W *ᵥ (x i)) + cc ⬝ᵥ (x i) := by
      intro i
      rw [hu, hsplit, ← hz₁, ← hz₂, ← hWz, ← hccz, inner_toE_vecMulVec, inner_toV]
    -- positive trace
    have htr : 0 < S.trace := by
      have hgt' : α < (nn : ℝ)⁻¹ * W.trace := by rw [← hfw]; exact hgt
      have hmul : α * (nn : ℝ) < W.trace := by
        have := mul_lt_mul_of_pos_right hgt' hnnR
        rw [inv_mul_eq_div, div_mul_cancel₀ _ (ne_of_gt hnnR)] at this
        exact this
      rw [hS, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_add,
        Matrix.trace_transpose, Matrix.trace_one]
      simp only [smul_eq_mul, Fintype.card_fin]
      linarith
    -- strict decrease at every active point
    have hactive : ∀ i, x i ⬝ᵥ x i = 1 →
        (x i) ⬝ᵥ (S *ᵥ (x i)) + (x i) ⬝ᵥ cc < 0 := by
      intro i hi
      have hmemU : u i ∈ convexHull ℝ U :=
        subset_convexHull ℝ U ⟨i, hi, rfl⟩
      have hui := hlt _ hmemU
      rw [hfu i] at hui
      have hquad : (x i) ⬝ᵥ (S *ᵥ (x i)) = (x i) ⬝ᵥ (W *ᵥ (x i)) - α := by
        rw [hS, sub_mulVec, dotProduct_sub, quad_symmetrize, smul_mulVec, Matrix.one_mulVec,
          dotProduct_smul, hi]
        simp
      rw [hquad, dotProduct_comm (x i) cc]
      linarith
    exact no_improving_direction x hball hmax S hSsymm cc htr hactive
