-- Prove2me | solution 1 for ConvexOptimization.lowner_john_polytope_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T17:13:33.683467+00:00
-- url     : https://prove2.me/submissions/fe6573cb-7bf1-4bb5-b299-1405fc954c24

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn
import Theorems.Thm_ConvexOptimization_lowner_john_unit_ball_kkt
import Theorems.Thm_ConvexOptimization_lowner_john_ball_subset_hull_of_kkt
import Theorems.Thm_ConvexOptimization_lowner_john_affine_invariant

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open Matrix
open ConvexOptimization

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace LJRAux

variable {nn : ℕ}

/-! ### Dot-product algebra -/

theorem dotProduct_self_nonneg (v : Fin nn → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem dotProduct_self_pos {v : Fin nn → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  rw [dotProduct]
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr (by simpa using hi)

theorem dotProduct_self_eq_zero {v : Fin nn → ℝ} (h : v ⬝ᵥ v = 0) : v = 0 := by
  by_contra hv
  exact absurd h (ne_of_gt (dotProduct_self_pos hv))

theorem dot_expand (p q : Fin nn → ℝ) :
    (p + q) ⬝ᵥ (p + q) = p ⬝ᵥ p + 2 * (p ⬝ᵥ q) + q ⬝ᵥ q := by
  simp only [dotProduct, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_expand_sub (p q : Fin nn → ℝ) :
    (p - q) ⬝ᵥ (p - q) = p ⬝ᵥ p - 2 * (p ⬝ᵥ q) + q ⬝ᵥ q := by
  simp only [dotProduct, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_smul_self (c : ℝ) (u : Fin nn → ℝ) : (c • u) ⬝ᵥ (c • u) = c ^ 2 * (u ⬝ᵥ u) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_mulVec_left (M : Matrix (Fin nn) (Fin nn) ℝ) (p q : Fin nn → ℝ) :
    (M *ᵥ p) ⬝ᵥ q = p ⬝ᵥ (Mᵀ *ᵥ q) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- A symmetric matrix whose quadratic form vanishes identically is zero. -/
theorem symm_quad_zero {M : Matrix (Fin nn) (Fin nn) ℝ} (hM : M.IsSymm)
    (h : ∀ v : Fin nn → ℝ, v ⬝ᵥ (M *ᵥ v) = 0) : M = 0 := by
  have hpol : ∀ p q : Fin nn → ℝ, p ⬝ᵥ (M *ᵥ q) = 0 := by
    intro p q
    have h1 := h (p + q)
    have h2 := h p
    have h3 := h q
    have hsym : q ⬝ᵥ (M *ᵥ p) = p ⬝ᵥ (M *ᵥ q) := by
      rw [dotProduct_comm q (M *ᵥ p), dot_mulVec_left, hM]
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct] at h1
    rw [hsym] at h1
    linarith
  ext i j
  have hkey := hpol (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at hkey
  simp only [Matrix.zero_apply]
  exact hkey

/-- Homogenisation: a bound on the quadratic form of `M` over the unit ball upgrades to a
bound over the whole space. -/
theorem homogenize (M : Matrix (Fin nn) (Fin nn) ℝ) (κ : ℝ)
    (h : ∀ v : Fin nn → ℝ, v ⬝ᵥ v ≤ 1 → (M *ᵥ v) ⬝ᵥ (M *ᵥ v) ≤ κ) :
    ∀ v : Fin nn → ℝ, (M *ᵥ v) ⬝ᵥ (M *ᵥ v) ≤ κ * (v ⬝ᵥ v) := by
  intro v
  by_cases hv : v = 0
  · subst hv
    have h0 := h 0 (by simp [dotProduct])
    simp [dotProduct] at h0 ⊢
  have hpos : 0 < v ⬝ᵥ v := dotProduct_self_pos hv
  set r : ℝ := Real.sqrt (v ⬝ᵥ v) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  have hu : (r⁻¹ • v) ⬝ᵥ (r⁻¹ • v) ≤ 1 := by
    rw [dot_smul_self, ← hr2]
    field_simp
    norm_num
  have hcore := h _ hu
  rw [Matrix.mulVec_smul, dot_smul_self] at hcore
  calc (M *ᵥ v) ⬝ᵥ (M *ᵥ v)
      = r ^ 2 * ((r⁻¹) ^ 2 * ((M *ᵥ v) ⬝ᵥ (M *ᵥ v))) := by field_simp
    _ ≤ r ^ 2 * κ := mul_le_mul_of_nonneg_left hcore (pow_pos hrpos 2).le
    _ = κ * (v ⬝ᵥ v) := by rw [hr2]; ring

/-- **Rigidity of the unit ball.**  A symmetric positive definite ellipsoid
`{v | ‖Av + b‖₂ ≤ 1}` that *equals* the Euclidean unit ball must be described by
`A = I`, `b = 0`. -/
theorem ellipsoid_eq_ball (hnn : 0 < nn) {A : Matrix (Fin nn) (Fin nn) ℝ} {b : Fin nn → ℝ}
    (hsymm : A.IsSymm) (hpd : A.PosDef)
    (h : ellipsoidBody A b = ellipsoidBody (1 : Matrix (Fin nn) (Fin nn) ℝ) 0) :
    A = 1 ∧ b = 0 := by
  classical
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hmem : ∀ v : Fin nn → ℝ, (A *ᵥ v + b) ⬝ᵥ (A *ᵥ v + b) ≤ 1 ↔ v ⬝ᵥ v ≤ 1 := by
    intro v
    have hx := Set.ext_iff.mp h v
    simpa [ellipsoidBody, Matrix.one_mulVec] using hx
  -- the forward bound
  have hfwd : ∀ v : Fin nn → ℝ, v ⬝ᵥ v ≤ 1 →
      (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ 1 - b ⬝ᵥ b := by
    intro v hv
    have h1 := (hmem v).mpr hv
    have h2 := (hmem (-v)).mpr (by simpa using hv)
    rw [dot_expand] at h1
    rw [Matrix.mulVec_neg, show -(A *ᵥ v) + b = b - A *ᵥ v by abel, dot_expand_sub] at h2
    rw [dotProduct_comm b (A *ᵥ v)] at h2
    linarith
  have hA := homogenize A (1 - b ⬝ᵥ b) hfwd
  -- the backward bound, obtained by substituting `v = A⁻¹ (z - b)`
  have hbwd : ∀ z : Fin nn → ℝ, z ⬝ᵥ z ≤ 1 →
      (A⁻¹ *ᵥ z) ⬝ᵥ (A⁻¹ *ᵥ z) ≤ 1 - (A⁻¹ *ᵥ b) ⬝ᵥ (A⁻¹ *ᵥ b) := by
    intro z hz
    have hcancel : ∀ w : Fin nn → ℝ, A *ᵥ (A⁻¹ *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
    have h1 : (A⁻¹ *ᵥ (z - b)) ⬝ᵥ (A⁻¹ *ᵥ (z - b)) ≤ 1 := by
      refine (hmem _).mp ?_
      rw [hcancel, sub_add_cancel]
      exact hz
    have h2 : (A⁻¹ *ᵥ (-z - b)) ⬝ᵥ (A⁻¹ *ᵥ (-z - b)) ≤ 1 := by
      refine (hmem _).mp ?_
      rw [hcancel, sub_add_cancel]
      simpa using hz
    have hp : A⁻¹ *ᵥ (z - b) = (A⁻¹ *ᵥ z) - (A⁻¹ *ᵥ b) := Matrix.mulVec_sub _ _ _
    have hnn' : A⁻¹ *ᵥ (-z - b) = -((A⁻¹ *ᵥ z) + (A⁻¹ *ᵥ b)) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_neg]; abel
    rw [hp, dot_expand_sub] at h1
    rw [hnn', neg_dotProduct_neg, dot_expand] at h2
    linarith
  have hAi := homogenize A⁻¹ (1 - (A⁻¹ *ᵥ b) ⬝ᵥ (A⁻¹ *ᵥ b)) hbwd
  -- lower bound on the quadratic form of `A`
  have hlow : ∀ v : Fin nn → ℝ,
      v ⬝ᵥ v ≤ (1 - (A⁻¹ *ᵥ b) ⬝ᵥ (A⁻¹ *ᵥ b)) * ((A *ᵥ v) ⬝ᵥ (A *ᵥ v)) := by
    intro v
    have hcv : A⁻¹ *ᵥ (A *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, Matrix.one_mulVec]
    have := hAi (A *ᵥ v)
    rwa [hcv] at this
  -- a unit vector
  obtain ⟨i₀⟩ : Nonempty (Fin nn) := ⟨⟨0, hnn⟩⟩
  set e : Fin nn → ℝ := Pi.single i₀ 1 with he
  have hee : e ⬝ᵥ e = 1 := by
    rw [he, dotProduct]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj; simp [hj]
    · intro hj; exact absurd (Finset.mem_univ i₀) hj
  have hene : e ≠ 0 := by
    intro hcon
    have : (1 : ℝ) = 0 := by
      have h0 := congrFun hcon i₀
      simp [he] at h0
    exact one_ne_zero this
  have hAene : A *ᵥ e ≠ 0 := by
    intro hcon
    apply hene
    have hcv : A⁻¹ *ᵥ (A *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, Matrix.one_mulVec]
    rw [← hcv, hcon, Matrix.mulVec_zero]
  have hAiene : A⁻¹ *ᵥ e ≠ 0 := by
    intro hcon
    apply hene
    have hcv : A *ᵥ (A⁻¹ *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
    rw [← hcv, hcon, Matrix.mulVec_zero]
  set κ : ℝ := 1 - b ⬝ᵥ b with hκ
  set μ : ℝ := 1 - (A⁻¹ *ᵥ b) ⬝ᵥ (A⁻¹ *ᵥ b) with hμ
  have hκle : κ ≤ 1 := by rw [hκ]; linarith [dotProduct_self_nonneg b]
  have hμle : μ ≤ 1 := by rw [hμ]; linarith [dotProduct_self_nonneg (A⁻¹ *ᵥ b)]
  have hκpos : 0 < κ := by
    have h1 := hA e
    rw [hee, mul_one] at h1
    exact lt_of_lt_of_le (dotProduct_self_pos hAene) h1
  have hμpos : 0 < μ := by
    have h1 := hAi e
    rw [hee, mul_one] at h1
    exact lt_of_lt_of_le (dotProduct_self_pos hAiene) h1
  have hprod : 1 ≤ κ * μ := by
    have h1 := hlow e
    rw [hee] at h1
    have h2 := hA e
    rw [hee, mul_one] at h2
    nlinarith [hμpos]
  have hκ1 : κ = 1 := by nlinarith
  have hμ1 : μ = 1 := by nlinarith
  -- `b = 0`
  have hb0 : b = 0 := by
    apply dotProduct_self_eq_zero
    rw [hκ] at hκ1
    linarith
  -- `A * A = 1`
  have hsq : A * A = 1 := by
    have hquad : ∀ v : Fin nn → ℝ, v ⬝ᵥ ((A * A - 1) *ᵥ v) = 0 := by
      intro v
      have h1 := hA v
      rw [hκ1, one_mul] at h1
      have h2 := hlow v
      rw [hμ1, one_mul] at h2
      have heq : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ v := le_antisymm h1 h2
      have hexp : v ⬝ᵥ ((A * A - 1) *ᵥ v) = (A *ᵥ v) ⬝ᵥ (A *ᵥ v) - v ⬝ᵥ v := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
          dotProduct_comm v (A *ᵥ (A *ᵥ v)), dot_mulVec_left, hsymm]
      rw [hexp, heq]
      ring
    have hsymm2 : (A * A - 1).IsSymm := by
      rw [Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hsymm]
    have := symm_quad_zero hsymm2 hquad
    have h3 : A * A - 1 = 0 := this
    linear_combination (norm := module) h3
  -- `A = 1`
  have hA1 : A = 1 := by
    have hAp : (A + 1).PosDef := hpd.add (Matrix.PosDef.one)
    have hApu : IsUnit (A + 1).det := isUnit_iff_ne_zero.mpr (ne_of_gt hAp.det_pos)
    have hfac : (A - 1) * (A + 1) = 0 := by
      have : (A - 1) * (A + 1) = A * A - 1 := by noncomm_ring
      rw [this, hsq, sub_self]
    have : A - 1 = 0 := by
      calc A - 1 = ((A - 1) * (A + 1)) * (A + 1)⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hApu, Matrix.mul_one]
        _ = 0 := by rw [hfac, Matrix.zero_mul]
    linear_combination (norm := module) this
  exact ⟨hA1, hb0⟩

/-- The affine map `v ↦ A v + b`. -/
noncomputable def affMap (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ) :
    (Fin nn → ℝ) →ᵃ[ℝ] (Fin nn → ℝ) :=
  AffineMap.mk' (fun w => A *ᵥ w + b) (Matrix.mulVecLin A) 0 (by intro p; simp)

@[simp] theorem affMap_apply (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ)
    (w : Fin nn → ℝ) : affMap A b w = A *ᵥ w + b := rfl

end LJRAux

open LJRAux in
/-- **Löwner–John rounding for a polytope** (B&V §8.4.1).  Shrinking the minimum-volume
covering ellipsoid of a finite point set by the factor `1/n` about its centre yields an
ellipsoid contained in the convex hull of the points. -/
theorem solution {nn m : ℕ} (hnn : 0 < nn)
    (x : Fin m → Fin nn → ℝ) (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ)
    (hopt : IsLownerJohn A b (Set.range x)) (v : Fin nn → ℝ)
    (hv : (A.mulVec v + b) ⬝ᵥ (A.mulVec v + b) ≤ 1 / (nn : ℝ) ^ 2) :
    v ∈ convexHull ℝ (Set.range x) := by
  classical
  have hAsymm : A.IsSymm := hopt.1
  have hApd : A.PosDef := hopt.2.1
  have hcov : Set.range x ⊆ ellipsoidBody A b := hopt.2.2.1
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hApd.det_pos)
  -- transport the optimum to the unit ball by the affine map `v ↦ Av + b`
  obtain ⟨A', b', hLJ', hbody'⟩ :=
    ConvexOptimization.lowner_john_affine_invariant A hunit b (Set.range x) A b hopt
  have hcancel : ∀ w : Fin nn → ℝ, A *ᵥ (A⁻¹ *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
  have hbodyeq : (fun w => A.mulVec w + b) '' ellipsoidBody A b
      = ellipsoidBody (1 : Matrix (Fin nn) (Fin nn) ℝ) 0 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [ellipsoidBody, Matrix.one_mulVec] using hw
    · intro hz
      refine ⟨A⁻¹ *ᵥ (z - b), ?_, ?_⟩
      · show (A *ᵥ (A⁻¹ *ᵥ (z - b)) + b) ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ (z - b)) + b) ≤ 1
        rw [hcancel, sub_add_cancel]
        simpa [ellipsoidBody, Matrix.one_mulVec] using hz
      · show A *ᵥ (A⁻¹ *ᵥ (z - b)) + b = z
        rw [hcancel, sub_add_cancel]
  obtain ⟨rfl, rfl⟩ :=
    ellipsoid_eq_ball hnn hLJ'.1 hLJ'.2.1 (hbody'.trans hbodyeq)
  -- the normalised point configuration
  set y : Fin m → Fin nn → ℝ := fun i => A *ᵥ x i + b with hy
  have hrange : (fun w => A.mulVec w + b) '' Set.range x = Set.range y := by
    rw [← Set.range_comp]
    rfl
  rw [hrange] at hLJ'
  -- the KKT multipliers at the normalised optimum
  obtain ⟨lam, hlnn, hI, hzero, hcs, -⟩ :=
    ConvexOptimization.lowner_john_unit_ball_kkt y hLJ'
  have hmemball :=
    ConvexOptimization.lowner_john_ball_subset_hull_of_kkt hnn y lam hlnn hI hzero hcs
      (A *ᵥ v + b) hv
  -- convex hulls transport along the affine map
  have himg : (affMap A b) '' Set.range x = Set.range y := hrange
  have hhull : convexHull ℝ (Set.range y) = (affMap A b) '' convexHull ℝ (Set.range x) := by
    rw [AffineMap.image_convexHull, himg]
  rw [hhull] at hmemball
  obtain ⟨v', hv', hveq⟩ := hmemball
  have hAeq : A *ᵥ v' = A *ᵥ v := by
    have : A *ᵥ v' + b = A *ᵥ v + b := hveq
    exact add_right_cancel this
  have hvv : v' = v := by
    have h1 := congrArg (fun w => A⁻¹ *ᵥ w) hAeq
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, Matrix.one_mulVec] at h1
    exact h1
  rwa [hvv] at hv'
