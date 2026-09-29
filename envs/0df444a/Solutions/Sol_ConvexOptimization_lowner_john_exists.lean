-- Prove2me | solution 1 for ConvexOptimization.lowner_john_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T05:26:43.928656+00:00
-- url     : https://prove2.me/submissions/960ab9e8-00bc-47ca-b999-0318f231668a

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal MatrixOrder
open MeasureTheory
open Matrix
open ConvexOptimization

namespace LJEAux

variable {nn : ℕ}

/-! ### Matrices and vectors inside Euclidean spaces -/

/-- Coordinatewise identification of matrices with a Euclidean space, used to give the
space of ellipsoid parameters a norm (hence compact closed balls). -/
noncomputable def toE (M : Matrix (Fin nn) (Fin nn) ℝ) :
    EuclideanSpace ℝ (Fin nn × Fin nn) := WithLp.toLp 2 (fun p => M p.1 p.2)

def ofE (y : EuclideanSpace ℝ (Fin nn × Fin nn)) : Matrix (Fin nn) (Fin nn) ℝ :=
  Matrix.of fun i j => y (i, j)

@[simp] theorem ofE_toE (M : Matrix (Fin nn) (Fin nn) ℝ) : ofE (toE M) = M := rfl

theorem inner_toE (M N : Matrix (Fin nn) (Fin nn) ℝ) :
    ⟪toE M, toE N⟫ = ∑ i, ∑ j, M i j * N i j := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp [toE, mul_comm]

theorem norm_toLp (v : Fin nn → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin nn))‖ = Real.sqrt (v ⬝ᵥ v) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, pow_two]

theorem abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [← sub_eq_add_neg, abs_neg] at h

theorem dotProduct_self_nonneg (v : Fin nn → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- A coordinate of a vector is bounded by the value of its quadratic form. -/
theorem sq_le_dotProduct (v : Fin nn → ℝ) (k : Fin nn) : v k * v k ≤ v ⬝ᵥ v :=
  Finset.single_le_sum (f := fun l => v l * v l) (fun l _ => mul_self_nonneg _)
    (Finset.mem_univ k)

theorem abs_le_one_of_dotProduct_le_one {v : Fin nn → ℝ} (h : v ⬝ᵥ v ≤ 1) (k : Fin nn) :
    |v k| ≤ 1 := by
  have h1 : v k * v k ≤ 1 := le_trans (sq_le_dotProduct v k) h
  nlinarith [abs_nonneg (v k), sq_abs (v k), abs_mul_abs_self (v k)]

theorem norm_toLp_le {v : Fin nn → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ k, |v k| ≤ C) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin nn))‖ ≤ (nn : ℝ) * C := by
  rw [norm_toLp]
  have hb : v ⬝ᵥ v ≤ ((nn : ℝ) * C) ^ 2 := by
    have h1 : v ⬝ᵥ v ≤ ∑ _k : Fin nn, C ^ 2 := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hk := h k
      nlinarith [abs_nonneg (v k), abs_mul_abs_self (v k)]
    have h2 : ∑ _k : Fin nn, C ^ 2 = (nn : ℝ) * C ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have h3 : (nn : ℝ) * C ^ 2 ≤ ((nn : ℝ) * C) ^ 2 := by
      have hn : (0 : ℝ) ≤ (nn : ℝ) := Nat.cast_nonneg nn
      rcases Nat.eq_zero_or_pos nn with h0 | hpos
      · simp [h0]
      · have : (1 : ℝ) ≤ (nn : ℝ) := by exact_mod_cast hpos
        nlinarith [sq_nonneg C]
    linarith [h1.trans_eq h2]
  calc Real.sqrt (v ⬝ᵥ v) ≤ Real.sqrt (((nn : ℝ) * C) ^ 2) := Real.sqrt_le_sqrt hb
    _ = (nn : ℝ) * C := Real.sqrt_sq (by positivity)

theorem norm_toE_le {A : Matrix (Fin nn) (Fin nn) ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i j, |A i j| ≤ C) : ‖toE A‖ ≤ (nn : ℝ) * C := by
  have hsq : ‖toE A‖ ^ 2 = ∑ i, ∑ j, A i j * A i j := by
    rw [← real_inner_self_eq_norm_sq, inner_toE]
  have hrow : ∀ i : Fin nn, ∑ j, A i j * A i j ≤ (nn : ℝ) * C ^ 2 := by
    intro i
    have h1 : ∑ j, A i j * A i j ≤ ∑ _j : Fin nn, C ^ 2 := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hk := h i j
      nlinarith [abs_nonneg (A i j), abs_mul_abs_self (A i j)]
    have h2 : ∑ _j : Fin nn, C ^ 2 = (nn : ℝ) * C ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    linarith [h1.trans_eq h2]
  have hb : ∑ i, ∑ j, A i j * A i j ≤ ((nn : ℝ) * C) ^ 2 := by
    have h1 : ∑ i, ∑ j, A i j * A i j ≤ ∑ _i : Fin nn, (nn : ℝ) * C ^ 2 :=
      Finset.sum_le_sum fun i _ => hrow i
    have h2 : ∑ _i : Fin nn, (nn : ℝ) * C ^ 2 = (nn : ℝ) * ((nn : ℝ) * C ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have h3 : (nn : ℝ) * ((nn : ℝ) * C ^ 2) = ((nn : ℝ) * C) ^ 2 := by ring
    linarith [h1.trans_eq h2, h3.le]
  nlinarith [norm_nonneg (toE A), hsq, hb,
    mul_nonneg (Nat.cast_nonneg nn : (0 : ℝ) ≤ (nn : ℝ)) hC]

/-! ### Ellipsoid bodies are convex -/

theorem mulVec_affine (A : Matrix (Fin nn) (Fin nn) ℝ) (b v w : Fin nn → ℝ) (a c : ℝ)
    (hac : a + c = 1) :
    A *ᵥ (a • v + c • w) + b = a • (A *ᵥ v + b) + c • (A *ᵥ w + b) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : ∑ j, A k j * (a * v j + c * w j)
      = a * (∑ j, A k j * v j) + c * (∑ j, A k j * w j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  have hc : c = 1 - a := by linarith
  subst hc
  ring

theorem convex_ellipsoidBody (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ) :
    Convex ℝ (ellipsoidBody A b) := by
  have hiff : ∀ u : Fin nn → ℝ,
      u ⬝ᵥ u ≤ 1 ↔ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin nn))‖ ≤ 1 := by
    intro u
    rw [norm_toLp]
    constructor
    · intro h
      calc Real.sqrt (u ⬝ᵥ u) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
        _ = 1 := Real.sqrt_one
    · intro h
      have := Real.sq_sqrt (dotProduct_self_nonneg u)
      nlinarith [Real.sqrt_nonneg (u ⬝ᵥ u)]
  intro v hv w hw a c ha hc hac
  simp only [ellipsoidBody, Set.mem_setOf_eq] at hv hw ⊢
  rw [hiff] at hv hw ⊢
  rw [mulVec_affine A b v w a c hac]
  have hlin : (WithLp.toLp 2 (a • (A *ᵥ v + b) + c • (A *ᵥ w + b))
      : EuclideanSpace ℝ (Fin nn))
      = a • (WithLp.toLp 2 (A *ᵥ v + b) : EuclideanSpace ℝ (Fin nn))
        + c • (WithLp.toLp 2 (A *ᵥ w + b) : EuclideanSpace ℝ (Fin nn)) := by
    ext k; rfl
  rw [hlin]
  calc ‖a • (WithLp.toLp 2 (A *ᵥ v + b) : EuclideanSpace ℝ (Fin nn))
        + c • (WithLp.toLp 2 (A *ᵥ w + b) : EuclideanSpace ℝ (Fin nn))‖
      ≤ ‖a • (WithLp.toLp 2 (A *ᵥ v + b) : EuclideanSpace ℝ (Fin nn))‖
        + ‖c • (WithLp.toLp 2 (A *ᵥ w + b) : EuclideanSpace ℝ (Fin nn))‖ := norm_add_le _ _
    _ = a * ‖(WithLp.toLp 2 (A *ᵥ v + b) : EuclideanSpace ℝ (Fin nn))‖
        + c * ‖(WithLp.toLp 2 (A *ᵥ w + b) : EuclideanSpace ℝ (Fin nn))‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg hc]
    _ ≤ a * 1 + c * 1 := by
        exact add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hc)
    _ = 1 := by rw [mul_one, mul_one, hac]

end LJEAux

open LJEAux in
theorem solution {nn m : ℕ} (x : Fin m → Fin nn → ℝ)
    (hfull : (interior (convexHull ℝ (Set.range x))).Nonempty) :
    ∃ (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ),
      IsLownerJohn A b (Set.range x) := by
  classical
  -- A ball inside the hull, from the full-dimensionality hypothesis.
  obtain ⟨c, hc⟩ := hfull
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  have hballsub : Metric.ball c r ⊆ convexHull ℝ (Set.range x) :=
    le_trans hball interior_subset
  -- The parameter space.
  set P := EuclideanSpace ℝ (Fin nn × Fin nn) × EuclideanSpace ℝ (Fin nn) with hPdef
  set q : P → Fin m → (Fin nn → ℝ) :=
    fun p i => (ofE p.1) *ᵥ x i + (WithLp.ofLp p.2) with hqdef
  -- A strictly feasible starting ellipsoid.
  set K : ℝ := 1 + ∑ i, (x i) ⬝ᵥ (x i) with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    have : (0 : ℝ) ≤ ∑ i, (x i) ⬝ᵥ (x i) :=
      Finset.sum_nonneg fun i _ => dotProduct_self_nonneg (x i)
    linarith
  have hKpos : (0 : ℝ) < K := by linarith
  set ε : ℝ := 1 / K with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεle : ε ≤ 1 := by
    rw [hεdef, div_le_one hKpos]; exact hK1
  set A₀ : Matrix (Fin nn) (Fin nn) ℝ := ε • (1 : Matrix (Fin nn) (Fin nn) ℝ) with hA₀def
  have hA₀mulVec : ∀ v : Fin nn → ℝ, A₀ *ᵥ v = ε • v := by
    intro v
    funext k
    simp only [hA₀def, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro hcon; exact absurd (Finset.mem_univ k) hcon
  have hA₀feas : ∀ i, (A₀ *ᵥ x i + 0) ⬝ᵥ (A₀ *ᵥ x i + 0) ≤ 1 := by
    intro i
    rw [add_zero, hA₀mulVec]
    have hsc : (ε • x i) ⬝ᵥ (ε • x i) = ε ^ 2 * ((x i) ⬝ᵥ (x i)) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsc]
    have hxi : (x i) ⬝ᵥ (x i) ≤ K := by
      rw [hKdef]
      have h1 : (x i) ⬝ᵥ (x i) ≤ ∑ j, (x j) ⬝ᵥ (x j) :=
        Finset.single_le_sum (f := fun j => (x j) ⬝ᵥ (x j))
          (fun j _ => dotProduct_self_nonneg (x j)) (Finset.mem_univ i)
      linarith
    have hε2 : ε ^ 2 = 1 / K ^ 2 := by rw [hεdef]; field_simp
    rw [hε2]
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith [hK1, dotProduct_self_nonneg (x i)]
  have hA₀det : A₀.det = ε ^ nn := by
    rw [hA₀def, Matrix.det_smul, Matrix.det_one, mul_one]
    simp
  set d₀ : ℝ := ε ^ nn with hd₀def
  have hd₀pos : 0 < d₀ := by rw [hd₀def]; positivity
  have hA₀psd : A₀.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, hA₀def, Matrix.smul_apply,
        Matrix.one_apply]
      by_cases h : j = i
      · simp [h]
      · simp [h, Ne.symm h]
    · intro v
      rw [show (star v : Fin nn → ℝ) = v from star_trivial v, hA₀mulVec]
      have : v ⬝ᵥ (ε • v) = ε * (v ⬝ᵥ v) := by
        simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this]
      exact mul_nonneg hεpos.le (dotProduct_self_nonneg v)
  -- The feasible set of parameters, cut down to a compact piece.
  set Feas : Set P := {p | (ofE p.1).PosSemidef ∧ (∀ i, (q p i) ⬝ᵥ (q p i) ≤ 1) ∧
    d₀ ≤ (ofE p.1).det} with hFeasdef
  have hp1 : ∀ s : Fin nn × Fin nn, Continuous fun p : P => p.1 s := fun s =>
    (PiLp.continuous_apply 2 (fun _ : Fin nn × Fin nn => ℝ) s).comp continuous_fst
  have hp2 : ∀ k : Fin nn, Continuous fun p : P => (WithLp.ofLp p.2 : Fin nn → ℝ) k := fun k =>
    (PiLp.continuous_apply 2 (fun _ : Fin nn => ℝ) k).comp continuous_snd
  have hcontM : Continuous fun p : P => ofE p.1 :=
    continuous_matrix fun i j => hp1 (i, j)
  have hcontMulVec : ∀ (v : Fin nn → ℝ) (k : Fin nn),
      Continuous fun p : P => ((ofE p.1) *ᵥ v) k := by
    intro v k
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (hp1 (k, j)).mul continuous_const
  have hcontq : ∀ (i : Fin m) (k : Fin nn), Continuous fun p : P => (q p i) k := by
    intro i k
    simp only [hqdef, Pi.add_apply]
    exact (hcontMulVec (x i) k).add (hp2 k)
  have hcontquad : ∀ i : Fin m, Continuous fun p : P => (q p i) ⬝ᵥ (q p i) := by
    intro i
    simp only [dotProduct]
    exact continuous_finsetSum _ fun k _ => (hcontq i k).mul (hcontq i k)
  have hclosed : IsClosed Feas := by
    have h1 : IsClosed {p : P | (ofE p.1).PosSemidef} := by
      have hrw : {p : P | (ofE p.1).PosSemidef}
          = (⋂ s : Fin nn × Fin nn, {p : P | (ofE p.1) s.2 s.1 = (ofE p.1) s.1 s.2})
            ∩ (⋂ v : Fin nn → ℝ, {p : P | 0 ≤ v ⬝ᵥ ((ofE p.1) *ᵥ v)}) := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
        rw [Matrix.posSemidef_iff_dotProduct_mulVec]
        constructor
        · rintro ⟨hh, hq⟩
          refine ⟨fun s => ?_, fun v => ?_⟩
          · have := congrFun (congrFun hh s.1) s.2
            simpa [Matrix.conjTranspose_apply] using this
          · have := hq v
            rwa [show (star v : Fin nn → ℝ) = v from star_trivial v] at this
        · rintro ⟨hs, hv⟩
          refine ⟨?_, fun v => ?_⟩
          · ext i j
            simpa [Matrix.conjTranspose_apply] using hs (i, j)
          · rw [show (star v : Fin nn → ℝ) = v from star_trivial v]
            exact hv v
      rw [hrw]
      refine IsClosed.inter (isClosed_iInter fun s => isClosed_eq ?_ ?_)
        (isClosed_iInter fun v => isClosed_le continuous_const ?_)
      · exact hp1 (s.2, s.1)
      · exact hp1 (s.1, s.2)
      · simp only [dotProduct]
        exact continuous_finsetSum _ fun k _ => continuous_const.mul (hcontMulVec v k)
    have h2 : IsClosed {p : P | ∀ i, (q p i) ⬝ᵥ (q p i) ≤ 1} := by
      have hrw : {p : P | ∀ i, (q p i) ⬝ᵥ (q p i) ≤ 1}
          = ⋂ i, {p : P | (q p i) ⬝ᵥ (q p i) ≤ 1} := by
        ext p; simp [Set.mem_iInter]
      rw [hrw]
      exact isClosed_iInter fun i => isClosed_le (hcontquad i) continuous_const
    have h3 : IsClosed {p : P | d₀ ≤ (ofE p.1).det} :=
      isClosed_le continuous_const hcontM.matrix_det
    have hFrw : Feas = ({p : P | (ofE p.1).PosSemidef}
        ∩ {p : P | ∀ i, (q p i) ⬝ᵥ (q p i) ≤ 1}) ∩ {p : P | d₀ ≤ (ofE p.1).det} := by
      rw [hFeasdef]
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [hFrw]
    exact (h1.inter h2).inter h3
  -- Every feasible ellipsoid contains the ball, hence has bounded parameters.
  have hbound : ∀ p ∈ Feas, ∀ i j, |(ofE p.1) i j| ≤ 4 / r := by
    intro p hp i j
    have hcov := hp.2.1
    set A := ofE p.1 with hAdef
    set b := (WithLp.ofLp p.2 : Fin nn → ℝ) with hbdef
    have hcover : Metric.ball c r ⊆ ellipsoidBody A b := by
      refine le_trans hballsub (convexHull_min ?_ (convex_ellipsoidBody A b))
      rintro _ ⟨i', rfl⟩
      exact hcov i'
    have hcmem : c ∈ Metric.ball c r := Metric.mem_ball_self hr
    have hu : (A *ᵥ c + b) ⬝ᵥ (A *ᵥ c + b) ≤ 1 := hcover hcmem
    set w : Fin nn → ℝ := fun k => if k = j then r / 2 else 0 with hwdef
    have hr2 : (0 : ℝ) < r / 2 := by linarith
    have hwnorm : ‖w‖ ≤ r / 2 := by
      refine (pi_norm_le_iff_of_nonneg hr2.le).mpr fun k => ?_
      simp only [hwdef]
      by_cases h : k = j
      · rw [if_pos h, Real.norm_eq_abs, abs_of_pos hr2]
      · rw [if_neg h, norm_zero]; linarith
    have hwmem : c + w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith
    have hs : (A *ᵥ (c + w) + b) ⬝ᵥ (A *ᵥ (c + w) + b) ≤ 1 := hcover hwmem
    have hsplit : A *ᵥ (c + w) + b = (A *ᵥ c + b) + A *ᵥ w := by
      rw [Matrix.mulVec_add]; abel
    have hcol : (A *ᵥ w) i = A i j * (r / 2) := by
      simp only [Matrix.mulVec, dotProduct, hwdef]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [hk]
      · intro hcon; exact absurd (Finset.mem_univ j) hcon
    have h1 : |((A *ᵥ c + b) + A *ᵥ w) i| ≤ 1 := by
      rw [← hsplit]; exact abs_le_one_of_dotProduct_le_one hs i
    have h2 : |(A *ᵥ c + b) i| ≤ 1 := abs_le_one_of_dotProduct_le_one hu i
    have h3 : |(A *ᵥ w) i| ≤ 2 := by
      have : (A *ᵥ w) i = ((A *ᵥ c + b) + A *ᵥ w) i - (A *ᵥ c + b) i := by
        simp [Pi.add_apply]
      rw [this]
      calc |((A *ᵥ c + b) + A *ᵥ w) i - (A *ᵥ c + b) i|
          ≤ |((A *ᵥ c + b) + A *ᵥ w) i| + |(A *ᵥ c + b) i| := abs_sub_le' _ _
        _ ≤ 2 := by linarith
    rw [hcol, abs_mul, abs_of_pos hr2] at h3
    rw [le_div_iff₀ hr]
    nlinarith [abs_nonneg (A i j), h3]
  have hboundb : ∀ p ∈ Feas, ∀ k, |(WithLp.ofLp p.2 : Fin nn → ℝ) k|
      ≤ 1 + (4 / r) * ∑ j, |c j| := by
    intro p hp k
    have hcov := hp.2.1
    set A := ofE p.1 with hAdef
    set b := (WithLp.ofLp p.2 : Fin nn → ℝ) with hbdef
    have hcover : Metric.ball c r ⊆ ellipsoidBody A b := by
      refine le_trans hballsub (convexHull_min ?_ (convex_ellipsoidBody A b))
      rintro _ ⟨i', rfl⟩
      exact hcov i'
    have hu : (A *ᵥ c + b) ⬝ᵥ (A *ᵥ c + b) ≤ 1 := hcover (Metric.mem_ball_self hr)
    have h2 : |(A *ᵥ c + b) k| ≤ 1 := abs_le_one_of_dotProduct_le_one hu k
    have h3 : |(A *ᵥ c) k| ≤ (4 / r) * ∑ j, |c j| := by
      simp only [Matrix.mulVec, dotProduct]
      calc |∑ j, A k j * c j| ≤ ∑ j, |A k j * c j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, (4 / r) * |c j| := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hbound p hp k j) (abs_nonneg _)
        _ = (4 / r) * ∑ j, |c j| := by rw [Finset.mul_sum]
    have hbk : b k = (A *ᵥ c + b) k - (A *ᵥ c) k := by simp [Pi.add_apply]
    rw [hbk]
    calc |(A *ᵥ c + b) k - (A *ᵥ c) k| ≤ |(A *ᵥ c + b) k| + |(A *ᵥ c) k| := abs_sub_le' _ _
      _ ≤ 1 + (4 / r) * ∑ j, |c j| := by linarith
  -- Compactness.
  set C₁ : ℝ := 4 / r with hC₁def
  set C₂ : ℝ := 1 + (4 / r) * ∑ j, |c j| with hC₂def
  have hC₁ : 0 ≤ C₁ := by rw [hC₁def]; exact div_nonneg (by norm_num) hr.le
  have hC₂ : 0 ≤ C₂ := by
    rw [hC₂def]
    have : (0 : ℝ) ≤ (4 / r) * ∑ j, |c j| :=
      mul_nonneg (div_nonneg (by norm_num) hr.le)
        (Finset.sum_nonneg fun j _ => abs_nonneg _)
    linarith
  set R : ℝ := (nn : ℝ) * C₁ + (nn : ℝ) * C₂ + 1 with hRdef
  have hsubball : Feas ⊆ Metric.closedBall (0 : P) R := by
    intro p hp
    have hA : ‖p.1‖ ≤ (nn : ℝ) * C₁ := by
      have := norm_toE_le hC₁ (hbound p hp)
      have hEq : toE (ofE p.1) = p.1 := by ext s; rfl
      rwa [hEq] at this
    have hb : ‖p.2‖ ≤ (nn : ℝ) * C₂ := by
      have := norm_toLp_le hC₂ (hboundb p hp)
      have hEq : (WithLp.toLp 2 (WithLp.ofLp p.2 : Fin nn → ℝ) :
        EuclideanSpace ℝ (Fin nn)) = p.2 := by ext k; rfl
      rwa [hEq] at this
    have hnA : (0 : ℝ) ≤ (nn : ℝ) * C₁ := by positivity
    have hnB : (0 : ℝ) ≤ (nn : ℝ) * C₂ := by positivity
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, hRdef]
    exact max_le (by linarith) (by linarith)
  have hcompact : IsCompact Feas :=
    (isCompact_closedBall (0 : P) R).of_isClosed_subset hclosed hsubball
  have hne : Feas.Nonempty := by
    refine ⟨(toE A₀, WithLp.toLp 2 (0 : Fin nn → ℝ)), ?_, ?_, ?_⟩
    · rw [ofE_toE]; exact hA₀psd
    · intro i
      have h0 : (WithLp.ofLp (WithLp.toLp 2 (0 : Fin nn → ℝ) : EuclideanSpace ℝ (Fin nn))
        : Fin nn → ℝ) = 0 := rfl
      simp only [hqdef, ofE_toE, h0]
      exact hA₀feas i
    · rw [ofE_toE, hA₀det]
  obtain ⟨p, hpFeas, hpmax⟩ := hcompact.exists_isMaxOn hne hcontM.matrix_det.continuousOn
  obtain ⟨hppsd, hpcov, hpdet⟩ := hpFeas
  refine ⟨ofE p.1, WithLp.ofLp p.2, hppsd.isHermitian, ?_, ?_, ?_⟩
  · exact (Matrix.PosSemidef.posDef_iff_det_ne_zero hppsd).mpr (by
      intro h; rw [h] at hpdet; linarith)
  · rintro _ ⟨i, rfl⟩
    exact hpcov i
  · intro A' b' hA'symm hA'pd hA'cov
    by_cases hdet : d₀ ≤ A'.det
    · have hmem : ((toE A', WithLp.toLp 2 b') : P) ∈ Feas := by
        refine ⟨by rw [ofE_toE]; exact hA'pd.posSemidef, fun i => ?_, by rw [ofE_toE]; exact hdet⟩
        have hb' : (WithLp.ofLp (WithLp.toLp 2 b' : EuclideanSpace ℝ (Fin nn)) : Fin nn → ℝ)
          = b' := rfl
        simp only [hqdef, ofE_toE, hb']
        exact hA'cov ⟨i, rfl⟩
      have hle : (ofE (toE A' : EuclideanSpace ℝ (Fin nn × Fin nn))).det ≤ (ofE p.1).det :=
        hpmax hmem
      rwa [ofE_toE] at hle
    · push_neg at hdet
      linarith
