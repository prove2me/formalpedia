-- Prove2me | solution 1 for FeaturePricing.Ellipsoid.min_eigenvalue_floor
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:03:01.724988+00:00
-- url     : https://prove2.me/submissions/093e5c0c-6945-4064-815d-3bedd2ebc05f

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing
import Definitions.Def_FeaturePricing_Ellipsoid_MinEigenvalue

set_option autoImplicit false
open Matrix LinearOptimization FeaturePricing.Ellipsoid MeasureTheory
open scoped MatrixOrder

/-- Cauchy–Schwarz for a positive semidefinite form. -/
theorem FPE_cs {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef)
    (v w : Fin d → ℝ) :
    (v ⬝ᵥ B *ᵥ w) ^ 2 ≤ (v ⬝ᵥ B *ᵥ v) * (w ⬝ᵥ B *ᵥ w) := by
  have hsymm : ∀ u u' : Fin d → ℝ, u ⬝ᵥ B *ᵥ u' = u' ⬝ᵥ B *ᵥ u := by
    intro u u'
    have h := hB.isHermitian
    have h' : Bᵀ = B := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using h.eq
    have e : u ᵥ* B = B *ᵥ u := by
      have := Matrix.vecMul_transpose B u
      rwa [h'] at this
    rw [Matrix.dotProduct_mulVec, e, dotProduct_comm]
  have key : ∀ t : ℝ, 0 ≤ (w ⬝ᵥ B *ᵥ w) * (t * t) + (2 * (v ⬝ᵥ B *ᵥ w)) * t + (v ⬝ᵥ B *ᵥ v) := by
    intro t
    have h0 := hB.dotProduct_mulVec_nonneg (v + t • w)
    have : (v + t • w) ⬝ᵥ B *ᵥ (v + t • w) =
        (w ⬝ᵥ B *ᵥ w) * (t * t) + (2 * (v ⬝ᵥ B *ᵥ w)) * t + (v ⬝ᵥ B *ᵥ v) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hsymm w v]
      ring
    simpa [this] using h0
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem FPE_psd_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ A *ᵥ x := hA.posSemidef.dotProduct_mulVec_nonneg x

theorem FPE_inv_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (x : Fin d → ℝ) :
    A⁻¹ *ᵥ (A *ᵥ x) = x := by
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]

/-- Every point of the ellipsoid has `|x'(θ - a)| ≤ √(x'Ax)`. -/
theorem FPE_ellipsoid_bound {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (x θ : Fin d → ℝ) (hθ : θ ∈ ellipsoid a A) :
    (x ⬝ᵥ θ - x ⬝ᵥ a) ^ 2 ≤ x ⬝ᵥ A *ᵥ x := by
  have h := FPE_cs A⁻¹ hA.inv.posSemidef (θ - a) (A *ᵥ x)
  rw [FPE_inv_mulVec A hA x] at h
  have e1 : (θ - a) ⬝ᵥ x = x ⬝ᵥ θ - x ⬝ᵥ a := by
    rw [dotProduct_comm, dotProduct_sub]
  have e2 : (A *ᵥ x) ⬝ᵥ x = x ⬝ᵥ A *ᵥ x := dotProduct_comm _ _
  rw [e1, e2] at h
  have hθ' : (θ - a) ⬝ᵥ A⁻¹ *ᵥ (θ - a) ≤ 1 := hθ
  have hq := FPE_psd_nonneg A hA x
  calc (x ⬝ᵥ θ - x ⬝ᵥ a) ^ 2 ≤ _ := h
    _ ≤ 1 * (x ⬝ᵥ A *ᵥ x) := mul_le_mul_of_nonneg_right hθ' hq
    _ = _ := one_mul _
-- Harry_Xu (LinearOptimization.ellipsoid_update_volume_lt, accepted solution): volume formula and determinant of the update
private def quadBall (n : ℕ) : Set (Fin n → ℝ) :=
  {x | x ⬝ᵥ x ≤ 1}

private theorem measurable_quadBall (n : ℕ) : MeasurableSet (quadBall n) := by
  apply IsClosed.measurableSet
  change IsClosed ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iic 1)
  exact isClosed_Iic.preimage (by fun_prop)

private theorem volume_quadBall_pos {n : ℕ} [Nonempty (Fin n)] :
    0 < volume (quadBall n) := by
  let U : Set (Fin n → ℝ) := {x | x ⬝ᵥ x < 1}
  have hUopen : IsOpen U := by
    change IsOpen ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iio 1)
    exact isOpen_Iio.preimage (by fun_prop)
  have hUne : U.Nonempty := by
    refine ⟨0, ?_⟩
    simp [U, dotProduct]
  exact (hUopen.measure_pos volume hUne).trans_le <|
    measure_mono fun x hx => by
      change x ⬝ᵥ x < 1 at hx
      exact le_of_lt hx

private theorem volume_quadBall_lt_top {n : ℕ} :
    volume (quadBall n) < ⊤ := by
  apply IsCompact.measure_lt_top
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · change IsClosed ((fun x : Fin n → ℝ => x ⬝ᵥ x) ⁻¹' Set.Iic 1)
    exact isClosed_Iic.preimage (by fun_prop)
  · apply Metric.isBounded_closedBall.subset
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    rw [Real.norm_eq_abs, abs_le]
    change x ⬝ᵥ x ≤ 1 at hx
    have hterm : x i ^ 2 ≤ x ⬝ᵥ x := by
      change x i ^ 2 ≤ ∑ j, x j * x j
      rw [sq]
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    constructor <;> nlinarith

private theorem ellipsoid_eq_preimage_invS {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef) :
    ellipsoid z D =
      (fun x => (CFC.sqrt D)⁻¹.mulVec (x - z)) ⁻¹' quadBall n := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt D
  have hSsymm : S⁻¹ᵀ = S⁻¹ := by
    simpa [S, Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      ((CFC.sqrt_nonneg D).posSemidef.isHermitian.inv.eq)
  have hDinvsq : D⁻¹ = S⁻¹ * S⁻¹ := by
    rw [← CFC.sq_sqrt D hD.posSemidef.nonneg]
    change (S ^ 2)⁻¹ = S⁻¹ * S⁻¹
    rw [← Matrix.inv_pow']
    simp [pow_two]
  ext x
  change ((x - z) ⬝ᵥ D⁻¹.mulVec (x - z) ≤ 1) ↔
    (S⁻¹.mulVec (x - z) ⬝ᵥ S⁻¹.mulVec (x - z) ≤ 1)
  rw [hDinvsq, ← Matrix.mulVec_mulVec]
  have hv : (x - z) ᵥ* S⁻¹ = S⁻¹ᵀ.mulVec (x - z) := by
    simpa using Matrix.vecMul_transpose S⁻¹ᵀ (x - z)
  rw [Matrix.dotProduct_mulVec, hv, hSsymm]

theorem ellipsoid_volume_formula {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef) :
    volume (ellipsoid z D) =
      ENNReal.ofReal (Real.sqrt D.det) * volume (quadBall n) := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt D
  have hSdet : S.det = Real.sqrt D.det := by
    simpa [S] using hD.posSemidef.det_sqrt
  have hdetpos : 0 < D.det := hD.det_pos
  have hSdetpos : 0 < S.det := by rw [hSdet]; positivity
  have hSinvdet : S⁻¹.det ≠ 0 := by
    have hsqrt0 : Real.sqrt D.det ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdetpos)
    simp [Matrix.det_nonsing_inv, hSdet, hsqrt0]
  rw [ellipsoid_eq_preimage_invS z D hD]
  -- Translation by `z` does not change volume.
  have htranslate :
      volume ((fun x => S⁻¹.mulVec (x - z)) ⁻¹' quadBall n) =
        volume ((fun x => S⁻¹.mulVec x) ⁻¹' quadBall n) := by
    let A : Set (Fin n → ℝ) := (fun x => S⁻¹.mulVec x) ⁻¹' quadBall n
    have hset :
        (fun x => S⁻¹.mulVec (x - z)) ⁻¹' quadBall n =
          (fun x => x + (-z)) ⁻¹' A := by
      ext x
      simp only [Set.mem_preimage, A]
      simp [sub_eq_add_neg]
    rw [hset, measure_preimage_add_right]
  rw [htranslate]
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hSinvdet
  have happly := congrArg (fun μ : Measure (Fin n → ℝ) => μ (quadBall n)) hmap
  change (Measure.map (Matrix.toLin' S⁻¹) volume) (quadBall n) =
    (ENNReal.ofReal |S⁻¹.det⁻¹| • volume) (quadBall n) at happly
  rw [Measure.map_apply (by fun_prop) (measurable_quadBall n), Measure.smul_apply] at happly
  simp only [smul_eq_mul] at happly
  change volume ((fun x => S⁻¹.mulVec x) ⁻¹' quadBall n) =
    ENNReal.ofReal |S⁻¹.det⁻¹| * volume (quadBall n) at happly
  rw [happly]
  congr 1
  rw [Matrix.det_nonsing_inv, hSdet]
  simp [Ring.inverse_eq_inv, abs_of_pos (Real.sqrt_pos.2 hdetpos)]

theorem det_one_sub_vecMulVec {n : ℕ} (u v : Fin n → ℝ) (c : ℝ) :
    det (1 - c • vecMulVec u v) = 1 - c * (v ⬝ᵥ u) := by
  classical
  have hmat :
      -(c • vecMulVec u v) =
        Matrix.replicateCol Unit (-(c • u)) * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, vecMulVec]
    ring
  rw [sub_eq_add_neg, hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ x, v x * -(c * u x)) = -c * (∑ x, v x * u x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hsum]
  ring

theorem ellipsoid_update_det {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a).det =
      (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n) *
        (((n : ℝ) - 1) / ((n : ℝ) + 1)) * D.det := by
  classical
  let q : ℝ := a ⬝ᵥ D.mulVec a
  let c : ℝ := 2 / ((n : ℝ) + 1)
  have hq : 0 < q := by
    dsimp [q]
    exact hD.dotProduct_mulVec_pos ha
  have hsymm : Dᵀ = D := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.isHermitian.eq
  have hrank : vecMulVec a a * D = vecMulVec a (D.mulVec a) := by
    ext i j
    simp only [Matrix.mul_apply, vecMulVec, Matrix.of_apply, mulVec, dotProduct]
    have hentry (x : Fin n) : D x j = D j x := by
      have := congrFun (congrFun hsymm j) x
      simpa using this
    simp_rw [hentry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hfactor :
      D - c • q⁻¹ • (D * vecMulVec a a * D) =
        D * (1 - (c * q⁻¹) • vecMulVec a (D.mulVec a)) := by
    rw [smul_smul]
    rw [Matrix.mul_assoc, hrank]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  unfold ellipsoidUpdateMatrix
  change det (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
      (D - c • q⁻¹ • (D * vecMulVec a a * D))) = _
  rw [hfactor, Matrix.det_smul, Matrix.det_mul,
    det_one_sub_vecMulVec]
  simp only [Fintype.card_fin]
  have hdot : D.mulVec a ⬝ᵥ a = q := by
    dsimp [q]
    rw [dotProduct_comm]
  rw [hdot]
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [c]
  field_simp [hq0]
  ring

-- Harry_Xu (LinearOptimization.ellipsoid_update_matrix_posDef, accepted solution)
theorem FPE_H_posDef {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (LinearOptimization.ellipsoidUpdateMatrix D a).PosDef := by
  classical
  have hq : 0 < a ⬝ᵥ D.mulVec a := hD.dotProduct_mulVec_pos ha
  have hDt : Dᵀ = D := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.isHermitian.eq
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · unfold LinearOptimization.ellipsoidUpdateMatrix
    apply Matrix.IsHermitian.smul
    · apply Matrix.IsHermitian.sub hD.isHermitian
      apply Matrix.IsHermitian.smul
      apply Matrix.IsHermitian.smul
      have haHerm : (vecMulVec a a : Matrix (Fin n) (Fin n) ℝ).IsHermitian := by
        ext i j
        simp [vecMulVec, mul_comm]
      simpa [hDt] using Matrix.isHermitian_mul_mul_conjTranspose D haHerm
      exact isSelfAdjoint_iff.mpr (by simp)
      exact isSelfAdjoint_iff.mpr (by simp)
    · exact isSelfAdjoint_iff.mpr (by simp)
  · intro x hx
    have hs : 0 < x ⬝ᵥ D.mulVec x := hD.dotProduct_mulVec_pos hx
    let q : ℝ := a ⬝ᵥ D.mulVec a
    let p : ℝ := a ⬝ᵥ D.mulVec x
    let s : ℝ := x ⬝ᵥ D.mulVec x
    have hq' : 0 < q := by simpa [q] using hq
    have hs' : 0 < s := by simpa [s] using hs
    have hnonneg := hD.posSemidef.dotProduct_mulVec_nonneg
      (x - (p / q) • a)
    have hsymm : x ⬝ᵥ D.mulVec a = p := by
      dsimp [p]
      have hv : x ᵥ* D = Dᵀ.mulVec x := by
        simpa using Matrix.vecMul_transpose Dᵀ x
      calc
        x ⬝ᵥ D.mulVec a = x ᵥ* D ⬝ᵥ a := Matrix.dotProduct_mulVec _ _ _
        _ = Dᵀ.mulVec x ⬝ᵥ a := by rw [hv]
        _ = D.mulVec x ⬝ᵥ a := by rw [hDt]
        _ = a ⬝ᵥ D.mulVec x := dotProduct_comm _ _
    have hcs : p ^ 2 ≤ q * s := by
      simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
        smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonneg
      rw [hsymm] at hnonneg
      change 0 ≤ s - (p / q) * p - (p / q) * (p - (p / q) * q) at hnonneg
      have hmul := mul_nonneg hq'.le hnonneg
      field_simp [ne_of_gt hq'] at hmul
      nlinarith
    have hquad :
        x ⬝ᵥ (D * vecMulVec a a * D).mulVec x = p ^ 2 := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.vecMulVec_mulVec]
      simp [Matrix.mulVec_smul, dotProduct_smul, hsymm, p, pow_two]
    unfold LinearOptimization.ellipsoidUpdateMatrix
    simp only [star_trivial, Matrix.smul_mulVec, Matrix.sub_mulVec,
      dotProduct_smul, dotProduct_sub, smul_eq_mul]
    rw [hquad]
    change 0 < ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) *
      (s - (2 / ((n : ℝ) + 1)) * (q⁻¹ * p ^ 2))
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
    have hden : 0 < (n : ℝ) ^ 2 - 1 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have hα : 0 < (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) :=
      div_pos (sq_pos_of_pos hnpos) hden
    have hγ0 : 0 ≤ (2 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hγ1 : (2 : ℝ) / ((n : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hpq : q⁻¹ * p ^ 2 ≤ s := by
      rw [inv_mul_eq_div, div_le_iff₀ hq']
      simpa [mul_comm] using hcs
    have hpq0 : 0 ≤ q⁻¹ * p ^ 2 := by positivity
    apply mul_pos hα
    nlinarith [mul_le_mul_of_nonneg_left hpq hγ0]
-- Harry_Xu (LinearOptimization.ellipsoid_update_halfspace_subset, accepted solution)
theorem test_update_inverse {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a)⁻¹ =
      ((((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) •
        (D⁻¹ + ((2 : ℝ) / ((n : ℝ) - 1)) •
          (a ⬝ᵥ D.mulVec a)⁻¹ • vecMulVec a a)) := by
  classical
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by nlinarith
  have hden : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hq : 0 < a ⬝ᵥ D.mulVec a := hD.dotProduct_mulVec_pos ha
  have hq0 : a ⬝ᵥ D.mulVec a ≠ 0 := ne_of_gt hq
  have hDunit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hrank :
      vecMulVec a a * D * vecMulVec a a =
        (a ⬝ᵥ D.mulVec a) • vecMulVec a a := by
    ext i j
    simp only [Matrix.mul_apply, vecMulVec, Matrix.of_apply, dotProduct, mulVec,
      Matrix.smul_apply, smul_eq_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  apply Matrix.inv_eq_left_inv
  unfold ellipsoidUpdateMatrix
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_sub]
  simp_rw [← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul D hDunit]
  simp only [Matrix.one_mul]
  rw [hrank]
  simp only [Matrix.smul_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
  field_simp [hn0, hn1, hden, hq0]
  ring_nf

theorem FPE_H_halfspace {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    ellipsoid z D ∩ {x | a ⬝ᵥ z ≤ a ⬝ᵥ x} ⊆
      ellipsoid (ellipsoidUpdateCenter z D a) (ellipsoidUpdateMatrix D a) := by
  classical
  rintro x ⟨hxE, hxH⟩
  unfold ellipsoid at hxE ⊢
  let y : Fin n → ℝ := x - z
  let u : Fin n → ℝ := D.mulVec a
  let q : ℝ := a ⬝ᵥ D.mulVec a
  let p : ℝ := a ⬝ᵥ y
  let s : ℝ := y ⬝ᵥ D⁻¹.mulVec y
  let c : ℝ := 1 / ((n : ℝ) + 1)
  let δ : ℝ := 2 / ((n : ℝ) - 1)
  let β : ℝ := ((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2
  let r : ℝ := Real.sqrt q
  change s ≤ 1 at hxE
  change a ⬝ᵥ z ≤ a ⬝ᵥ x at hxH
  have hp : 0 ≤ p := by
    dsimp [p, y]
    rw [dotProduct_sub]
    linarith
  have hq : 0 < q := by
    dsimp [q]
    exact hD.dotProduct_mulVec_pos ha
  have hr0 : 0 ≤ r := by simp [r]
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hr2 : r ^ 2 = q := by simp [r, Real.sq_sqrt hq.le]
  have hDunit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hu : u ≠ 0 := by
    intro hu0
    have h := congrArg (D⁻¹.mulVec) hu0
    dsimp [u] at h
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hDunit] at h
    have : a = 0 := by simpa using h
    exact ha this
  have hDinvT : D⁻¹ᵀ = D⁻¹ := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hD.inv.isHermitian.eq
  have hsymmInv (v w : Fin n → ℝ) :
      v ⬝ᵥ D⁻¹.mulVec w = w ⬝ᵥ D⁻¹.mulVec v := by
    have hv : v ᵥ* D⁻¹ = D⁻¹ᵀ.mulVec v := by
      simpa using Matrix.vecMul_transpose D⁻¹ᵀ v
    calc
      v ⬝ᵥ D⁻¹.mulVec w = v ᵥ* D⁻¹ ⬝ᵥ w := Matrix.dotProduct_mulVec _ _ _
      _ = D⁻¹ᵀ.mulVec v ⬝ᵥ w := by rw [hv]
      _ = D⁻¹.mulVec v ⬝ᵥ w := by rw [hDinvT]
      _ = w ⬝ᵥ D⁻¹.mulVec v := dotProduct_comm _ _
  have hinvDmul (v : Fin n → ℝ) : D⁻¹.mulVec (D.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hDunit]
    simp
  have hqu : u ⬝ᵥ D⁻¹.mulVec u = q := by
    rw [hsymmInv]
    simp [u, q, hinvDmul, dotProduct_comm]
  have hpu : u ⬝ᵥ D⁻¹.mulVec y = p := by
    rw [hsymmInv]
    simp [u, p, hinvDmul, dotProduct_comm]
  have hcs : p ^ 2 ≤ q * s := by
    have hnonneg := hD.inv.posSemidef.dotProduct_mulVec_nonneg
      (y - (p / q) • u)
    simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
      smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonneg
    rw [hpu, hsymmInv y u, hpu, hqu] at hnonneg
    change 0 ≤ s - (p / q) * p - (p / q) * (p - (p / q) * q) at hnonneg
    have hmul := mul_nonneg hq.le hnonneg
    field_simp [ne_of_gt hq] at hmul
    nlinarith
  let t : ℝ := p / r
  have ht0 : 0 ≤ t := div_nonneg hp hr0
  have ht1 : t ≤ 1 := by
    have hp2q : p ^ 2 ≤ q := by nlinarith [mul_le_mul_of_nonneg_left hxE hq.le]
    dsimp [t]
    rw [div_le_one hr]
    nlinarith
  have hyb :
      x - ellipsoidUpdateCenter z D a = y - (c / r) • u := by
    ext i
    simp only [ellipsoidUpdateCenter, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    dsimp [y, u, c, r, q]
    field_simp [ne_of_gt hr]
    ring
  change (x - ellipsoidUpdateCenter z D a) ⬝ᵥ
      (ellipsoidUpdateMatrix D a)⁻¹.mulVec
        (x - ellipsoidUpdateCenter z D a) ≤ 1
  rw [test_update_inverse hn D hD a ha, hyb]
  change (y - (c / r) • u) ⬝ᵥ
      (β • (D⁻¹ + δ • q⁻¹ • vecMulVec a a)).mulVec
        (y - (c / r) • u) ≤ 1
  have hay : a ⬝ᵥ y = p := rfl
  have hau : a ⬝ᵥ u = q := rfl
  have hya : y ⬝ᵥ a = p := (dotProduct_comm y a).trans hay
  have hua : u ⬝ᵥ a = q := (dotProduct_comm u a).trans hau
  have hcalc :
      (y - (c / r) • u) ⬝ᵥ
          (β • (D⁻¹ + δ • q⁻¹ • vecMulVec a a)).mulVec
            (y - (c / r) • u) =
        β * (s + δ * t ^ 2 - (2 / ((n : ℝ) - 1)) * t +
          1 / ((n : ℝ) ^ 2 - 1)) := by
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_smul, Matrix.vecMulVec_mulVec, sub_dotProduct,
      smul_dotProduct, dotProduct_sub, dotProduct_smul, add_dotProduct,
      dotProduct_add, op_smul_eq_smul, smul_eq_mul]
    rw [hpu, hsymmInv y u, hpu, hqu]
    simp only [hay, hau, hya, hua]
    have hnR' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnm1 : (n : ℝ) - 1 ≠ 0 := by nlinarith
    have hnp1 : (n : ℝ) + 1 ≠ 0 := by nlinarith
    have hnsq1 : (n : ℝ) ^ 2 - 1 ≠ 0 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    dsimp [β, δ, c, t, s]
    rw [← hr2]
    field_simp [ne_of_gt hq, ne_of_gt hr, hnm1, hnp1, hnsq1]
    ring_nf
  rw [hcalc]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hdenpos : 0 < (n : ℝ) ^ 2 - 1 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hβ : 0 < β := by
    dsimp [β]
    positivity
  have htquad : t ^ 2 - t ≤ 0 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  dsimp [δ]
  have hinside :
      s + (2 / ((n : ℝ) - 1)) * t ^ 2 -
          (2 / ((n : ℝ) - 1)) * t + 1 / ((n : ℝ) ^ 2 - 1) ≤
        1 + 1 / ((n : ℝ) ^ 2 - 1) := by
    have hcoef : 0 ≤ (2 : ℝ) / ((n : ℝ) - 1) := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef htquad]
  have hβid : β * (1 + 1 / ((n : ℝ) ^ 2 - 1)) = 1 := by
    dsimp [β]
    field_simp [ne_of_gt hn0, ne_of_gt hdenpos]
    ring_nf
  calc
    β * (s + 2 / (↑n - 1) * t ^ 2 - 2 / (↑n - 1) * t +
      1 / (↑n ^ 2 - 1))
        ≤ β * (1 + 1 / (↑n ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left hinside hβ.le
    _ = 1 := hβid

theorem FPE_upd_neg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ellipsoidUpdateMatrix A (-x) = ellipsoidUpdateMatrix A x := by
  unfold ellipsoidUpdateMatrix
  have h1 : vecMulVec (-x) (-x) = (vecMulVec x x : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j; simp [vecMulVec]
  have h2 : (-x) ⬝ᵥ A.mulVec (-x) = x ⬝ᵥ A.mulVec x := by
    simp [Matrix.mulVec_neg]
  rw [h1, h2]

theorem FPE_gap {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    bHigh a A x - bLow a A x = 2 * Real.sqrt (x ⬝ᵥ A *ᵥ x) := by
  unfold bHigh bLow; ring

theorem FPE_priceOf_explore {d : ℕ} (ε : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (h : ε < bHigh a A x - bLow a A x) : priceOf ε a A x = x ⬝ᵥ a := by
  unfold priceOf
  rw [if_neg (not_le.2 h)]
  unfold bHigh bLow; ring

theorem FPE_explore_ne {d : ℕ} {ε : ℝ} (hε : 0 < ε) (a : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) (h : ε < bHigh a A x - bLow a A x) :
    x ≠ 0 := by
  intro hx
  subst hx
  rw [FPE_gap] at h
  simp at h
  linarith

/-- Positive definiteness and `θ ∈ E_t` along every run. -/
theorem FPE_invariant {d : ℕ} (hd : 2 ≤ d) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (θ : Fin d → ℝ) (hθ : θ ⬝ᵥ θ ≤ R ^ 2) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    (shape R ε θ x t).PosDef ∧ θ ∈ ellipsoid (center R ε θ x t) (shape R ε θ x t) := by
  induction t with
  | zero =>
    have hR2 : 0 < R ^ 2 := by positivity
    have hP : ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := by
      exact Matrix.PosDef.one.smul hR2
    refine ⟨hP, ?_⟩
    show θ ∈ ellipsoid (0 : Fin d → ℝ) ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))
    have hinv : ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = (R ^ 2)⁻¹ • 1 := by
      apply Matrix.inv_eq_right_inv
      rw [smul_mul_smul_comm, mul_inv_cancel₀ hR2.ne']
      simp
    show (θ - 0) ⬝ᵥ ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (θ - 0) ≤ 1
    rw [hinv]
    simp only [sub_zero, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [inv_mul_eq_div, div_le_one hR2]
    exact hθ
  | succ t ih =>
    obtain ⟨hPD, hmem⟩ := ih
    have hst : state R ε θ x (t + 1) = step ε θ (x t) (state R ε θ x t) := rfl
    unfold shape center
    rw [hst]
    unfold step
    by_cases hg : bHigh (state R ε θ x t).1 (state R ε θ x t).2 (x t) -
        bLow (state R ε θ x t).1 (state R ε θ x t).2 (x t) ≤ ε
    · rw [if_pos hg]; exact ⟨hPD, hmem⟩
    · rw [if_neg hg]
      have hg' := not_le.1 hg
      have hx0 : x t ≠ 0 := FPE_explore_ne hε _ _ _ hg'
      have hp := FPE_priceOf_explore ε _ _ _ hg'
      have hPD' := FPE_H_posDef hd _ hPD (x t) hx0
      by_cases hs : priceOf ε (state R ε θ x t).1 (state R ε θ x t).2 (x t) ≤ θ ⬝ᵥ x t
      · rw [if_pos hs]
        refine ⟨hPD', ?_⟩
        rw [hp] at hs
        exact FPE_H_halfspace hd _ _ hPD (x t) hx0
          ⟨hmem, by simpa [dotProduct_comm] using hs⟩
      · rw [if_neg hs]
        rw [hp] at hs
        have hs' : θ ⬝ᵥ x t < x t ⬝ᵥ (state R ε θ x t).1 := not_le.1 hs
        have hx0' : -x t ≠ 0 := neg_ne_zero.2 hx0
        refine ⟨?_, ?_⟩
        · rw [← FPE_upd_neg]; exact FPE_H_posDef hd _ hPD _ hx0'
        · rw [← FPE_upd_neg]
          exact FPE_H_halfspace hd _ _ hPD (-x t) hx0'
            ⟨hmem, by
              have hs'' : x t ⬝ᵥ θ < x t ⬝ᵥ center R ε θ x t := by
                rw [dotProduct_comm θ] at hs'; exact hs'
              show (-x t) ⬝ᵥ center R ε θ x t ≤ (-x t) ⬝ᵥ θ
              simp only [neg_dotProduct]
              linarith⟩

theorem FPE_spec_shift {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) :
    spectrum ℝ (A - c • (1 : Matrix (Fin d) (Fin d) ℝ)) = (fun s => s - c) '' spectrum ℝ A := by
  have h := spectrum.sub_singleton_eq A c
  rw [Algebra.algebraMap_eq_smul_one] at h
  rw [← h]
  ext y
  simp [Set.mem_sub]

theorem FPE_herm_shift {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (c : ℝ) :
    (A - c • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian := by
  unfold Matrix.IsHermitian at *
  rw [Matrix.conjTranspose_sub, hA, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

theorem FPE_psd_iff {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (c : ℝ) :
    (A - c • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ↔ ∀ s ∈ spectrum ℝ A, c ≤ s := by
  have hH := FPE_herm_shift A hA c
  rw [hH.posSemidef_iff_eigenvalues_nonneg]
  constructor
  · intro h s hs
    have : s - c ∈ spectrum ℝ (A - c • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
      rw [FPE_spec_shift]; exact ⟨s, hs, rfl⟩
    rw [hH.spectrum_real_eq_range_eigenvalues] at this
    obtain ⟨i, hi⟩ := this
    have := h i
    simp only [Pi.zero_apply] at this
    linarith
  · intro h i
    have hm := hH.eigenvalues_mem_spectrum_real i
    rw [FPE_spec_shift] at hm
    obtain ⟨s, hs, hse⟩ := hm
    have := h s hs
    simp only [Pi.zero_apply]
    linarith

theorem FPE_spec_bdd {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    BddBelow (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).bddBelow

theorem FPE_spec_ne {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    (spectrum ℝ A).Nonempty := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact Set.range_nonempty _

/-- Rayleigh lower bound: `λ_min ‖v‖² ≤ v'Av`. -/
theorem FPE_lamMin_le_quad {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (v : Fin d → ℝ) : lamMin A * (v ⬝ᵥ v) ≤ v ⬝ᵥ A *ᵥ v := by
  have h := (FPE_psd_iff A hA (lamMin A)).2 (fun s hs => csInf_le (FPE_spec_bdd A hA) hs)
  have := h.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at this
  linarith

/-- Converse: a uniform Rayleigh lower bound bounds `λ_min` from below. -/
theorem FPE_le_lamMin {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (c : ℝ) (h : ∀ v : Fin d → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ A *ᵥ v) : c ≤ lamMin A := by
  have hP : (A - c • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (FPE_herm_shift A hA c) ?_
    intro v
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith [h v]
  exact le_csInf (FPE_spec_ne hd A hA) ((FPE_psd_iff A hA c).1 hP)

theorem FPE_lamMin_pos {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) :
    0 < lamMin A := by
  rw [lamMin, hA.isHermitian.spectrum_real_eq_range_eigenvalues]
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne := Set.range_nonempty hA.isHermitian.eigenvalues
  obtain ⟨i, hi⟩ := hne.csInf_mem (Set.finite_range hA.isHermitian.eigenvalues)
  rw [← hi]
  exact hA.eigenvalues_pos i

theorem FPE_symm {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.IsHermitian)
    (u u' : Fin d → ℝ) : u ⬝ᵥ B *ᵥ u' = u' ⬝ᵥ B *ᵥ u := by
  have h' : Bᵀ = B := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using hB.eq
  have e : u ᵥ* B = B *ᵥ u := by
    have := Matrix.vecMul_transpose B u
    rwa [h'] at this
  rw [Matrix.dotProduct_mulVec, e, dotProduct_comm]

/-- The quadratic form of the updated matrix. -/
theorem FPE_upd_quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (x v : Fin d → ℝ) :
    v ⬝ᵥ (ellipsoidUpdateMatrix A x) *ᵥ v =
      ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
        (v ⬝ᵥ A *ᵥ v - (2 / ((d : ℝ) + 1)) * ((x ⬝ᵥ A *ᵥ x)⁻¹ * (v ⬝ᵥ A *ᵥ x) ^ 2)) := by
  have hquad : v ⬝ᵥ (A * vecMulVec x x * A) *ᵥ v = (v ⬝ᵥ A *ᵥ x) ^ 2 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec]
    simp only [Matrix.mulVec_smul, dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
    rw [FPE_symm A hA x v]
    ring
  unfold ellipsoidUpdateMatrix
  simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub, smul_eq_mul]
  rw [hquad]

theorem FPE_shape_succ {d : ℕ} (R ε : ℝ) (θ : Fin d → ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    (¬ isExplore R ε θ x t ∧ shape R ε θ x (t + 1) = shape R ε θ x t) ∨
    (isExplore R ε θ x t ∧
      shape R ε θ x (t + 1) = ellipsoidUpdateMatrix (shape R ε θ x t) (x t)) := by
  have hst : state R ε θ x (t + 1) = step ε θ (x t) (state R ε θ x t) := rfl
  unfold shape isExplore center
  rw [hst]
  unfold step
  by_cases hg : bHigh (state R ε θ x t).1 (state R ε θ x t).2 (x t) -
      bLow (state R ε θ x t).1 (state R ε θ x t).2 (x t) ≤ ε
  · rw [if_pos hg]
    left
    exact ⟨not_lt.2 hg, rfl⟩
  · rw [if_neg hg]
    right
    refine ⟨not_le.1 hg, ?_⟩
    by_cases hs : priceOf ε (state R ε θ x t).1 (state R ε θ x t).2 (x t) ≤ θ ⬝ᵥ x t
    · rw [if_pos hs]
    · rw [if_neg hs]

theorem FPE_explore_q {d : ℕ} {R ε : ℝ} (hε : 0 < ε) (θ : Fin d → ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ)
    (h : isExplore R ε θ x t) : ε ^ 2 / 4 < x t ⬝ᵥ shape R ε θ x t *ᵥ x t := by
  unfold isExplore at h
  rw [FPE_gap] at h
  have h2 : ε / 2 < Real.sqrt (x t ⬝ᵥ shape R ε θ x t *ᵥ x t) := by linarith
  have h3 := Real.lt_sqrt (by positivity : (0:ℝ) ≤ ε / 2) |>.1 h2
  nlinarith

theorem FPE_lemma3 {d : ℕ} (hd : 2 ≤ d) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (x : Fin d → ℝ) (hx : x ≠ 0) :
    (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 * lamMin A ≤ lamMin (ellipsoidUpdateMatrix A x) := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hPD := FPE_H_posDef hd A hA x hx
  have hq : 0 < x ⬝ᵥ A *ᵥ x := by
    have := hA.dotProduct_mulVec_pos hx
    simpa using this
  have hden : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  apply FPE_le_lamMin hd0 _ hPD.isHermitian
  intro v
  rw [FPE_upd_quad A hA.isHermitian x v]
  have hcs := FPE_cs A hA.posSemidef v x
  have hlam := FPE_lamMin_le_quad hd0 A hA.isHermitian v
  have hp : (x ⬝ᵥ A *ᵥ x)⁻¹ * (v ⬝ᵥ A *ᵥ x) ^ 2 ≤ v ⬝ᵥ A *ᵥ v := by
    rw [inv_mul_le_iff₀ hq]
    linarith
  have hg : 0 ≤ (2 : ℝ) / ((d : ℝ) + 1) := by positivity
  have h1 : (v ⬝ᵥ A *ᵥ v) * (1 - 2 / ((d : ℝ) + 1)) ≤
      v ⬝ᵥ A *ᵥ v - (2 / ((d : ℝ) + 1)) * ((x ⬝ᵥ A *ᵥ x)⁻¹ * (v ⬝ᵥ A *ᵥ x) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hp hg]
  have hcoef : 0 ≤ (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 hcoef
  have hid : (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) * (1 - 2 / ((d : ℝ) + 1)) =
      (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 := by
    have : (d : ℝ) + 1 ≠ 0 := by linarith
    have : (d : ℝ) ^ 2 - 1 ≠ 0 := hden.ne'
    field_simp
    ring
  have hpos : 0 ≤ (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hlam hpos
  calc (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 * lamMin A * (v ⬝ᵥ v)
      = (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 * (lamMin A * (v ⬝ᵥ v)) := by ring
    _ ≤ (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 * (v ⬝ᵥ A *ᵥ v) := h3
    _ = (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) * ((v ⬝ᵥ A *ᵥ v) * (1 - 2 / ((d : ℝ) + 1))) := by
        rw [← hid]; ring
    _ ≤ _ := h2

theorem FPE_dot_nonneg {d : ℕ} (u : Fin d → ℝ) : 0 ≤ u ⬝ᵥ u := by
  simp only [dotProduct]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

theorem FPE_B_quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ : ℝ) (v w : Fin d → ℝ) :
    v ⬝ᵥ (A - μ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ w = v ⬝ᵥ A *ᵥ w - μ * (v ⬝ᵥ w) := by
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]

/-- Core inequality of Lemma 4: `γ (v'Ax)² ≤ q · v'(A - μ I)v`. -/
theorem FPE_L4_core {d : ℕ} (hd : 2 ≤ d) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (x : Fin d → ℝ) (hx : x ⬝ᵥ x ≤ 1)
    (hq : 100 * (d : ℝ) ^ 2 * lamMin A < x ⬝ᵥ A *ᵥ x) (v : Fin d → ℝ) :
    (2 / ((d : ℝ) + 1)) * (v ⬝ᵥ A *ᵥ x) ^ 2 ≤
      (x ⬝ᵥ A *ᵥ x) * (v ⬝ᵥ A *ᵥ v - (lamMin A - lamMin A / (d : ℝ) ^ 2) * (v ⬝ᵥ v)) := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  set lam := lamMin A with hlam
  have hlpos : 0 < lam := FPE_lamMin_pos hd0 A hA
  set μ : ℝ := lam - lam / (d : ℝ) ^ 2 with hμ
  have hm : 0 < lam / (d : ℝ) ^ 2 := by positivity
  have hμ0 : 0 ≤ μ := by
    have : lam / (d : ℝ) ^ 2 ≤ lam := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hμl : μ ≤ lam := by linarith
  set B : Matrix (Fin d) (Fin d) ℝ := A - μ • (1 : Matrix (Fin d) (Fin d) ℝ) with hB
  have hBq := FPE_B_quad A μ
  have hlow : ∀ u : Fin d → ℝ, (lam / (d : ℝ) ^ 2) * (u ⬝ᵥ u) ≤ u ⬝ᵥ B *ᵥ u := by
    intro u
    rw [hB, hBq]
    have := FPE_lamMin_le_quad hd0 A hA.isHermitian u
    rw [← hlam] at this
    have h2 : (lam - μ) = lam / (d : ℝ) ^ 2 := by rw [hμ]; ring
    nlinarith [this]
  have hBpsd : B.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (FPE_herm_shift A hA.isHermitian μ) ?_
    intro u
    have h1 := hlow u
    have h2 : 0 ≤ u ⬝ᵥ u := FPE_dot_nonneg u
    simp only [star_trivial]
    nlinarith
  set q := x ⬝ᵥ A *ᵥ x with hqdef
  have hqpos : 0 < q := by nlinarith [mul_pos (by positivity : (0:ℝ) < 100 * (d:ℝ)^2) hlpos]
  set W := v ⬝ᵥ B *ᵥ v with hW
  have hW0 : 0 ≤ W := hBpsd.dotProduct_mulVec_nonneg v
  -- p = v'Bx + μ v'x
  have hp : v ⬝ᵥ A *ᵥ x = v ⬝ᵥ B *ᵥ x + μ * (v ⬝ᵥ x) := by rw [hB, hBq]; ring
  have hcs1 := FPE_cs B hBpsd v x
  have hxB : x ⬝ᵥ B *ᵥ x ≤ q := by
    rw [hB, hBq]
    have : 0 ≤ μ * (x ⬝ᵥ x) := mul_nonneg hμ0 (FPE_dot_nonneg x)
    linarith
  have hxB0 : 0 ≤ x ⬝ᵥ B *ᵥ x := hBpsd.dotProduct_mulVec_nonneg x
  have hbx : (v ⬝ᵥ B *ᵥ x) ^ 2 ≤ W * q := by
    calc (v ⬝ᵥ B *ᵥ x) ^ 2 ≤ W * (x ⬝ᵥ B *ᵥ x) := hcs1
      _ ≤ W * q := mul_le_mul_of_nonneg_left hxB hW0
  -- (v'x)^2 ≤ v'v
  have hvx : (v ⬝ᵥ x) ^ 2 ≤ v ⬝ᵥ v := by
    have h1 := FPE_cs (1 : Matrix (Fin d) (Fin d) ℝ) Matrix.PosSemidef.one v x
    simp only [Matrix.one_mulVec] at h1
    have hvv : 0 ≤ v ⬝ᵥ v := FPE_dot_nonneg v
    nlinarith [mul_le_mul_of_nonneg_left hx hvv]
  -- v'v ≤ d²/lam * W
  have hvv : (v ⬝ᵥ v) * (lam / (d : ℝ) ^ 2) ≤ W := by
    have := hlow v; rw [← hW] at this; linarith
  have hmu : μ ^ 2 * (v ⬝ᵥ v) ≤ (d : ℝ) ^ 2 * lam * W := by
    have h1 : μ ^ 2 ≤ lam ^ 2 := by nlinarith
    have h2 : (v ⬝ᵥ v) ≤ (d : ℝ) ^ 2 / lam * W := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlpos]
      have e : (v ⬝ᵥ v) * lam = (v ⬝ᵥ v) * (lam / (d : ℝ) ^ 2) * (d : ℝ) ^ 2 := by
        field_simp
      rw [e, mul_comm ((d : ℝ) ^ 2) W]
      exact mul_le_mul_of_nonneg_right hvv (by positivity)
    have hvv0 : 0 ≤ v ⬝ᵥ v := FPE_dot_nonneg v
    calc μ ^ 2 * (v ⬝ᵥ v) ≤ lam ^ 2 * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_right h1 hvv0
      _ ≤ lam ^ 2 * ((d : ℝ) ^ 2 / lam * W) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (d : ℝ) ^ 2 * lam * W := by field_simp
  -- (a+b)^2 ≤ 5/4 a^2 + 5 b^2
  have hsq : (v ⬝ᵥ A *ᵥ x) ^ 2 ≤ (5 / 4) * (v ⬝ᵥ B *ᵥ x) ^ 2 + 5 * (μ * (v ⬝ᵥ x)) ^ 2 := by
    rw [hp]; nlinarith [sq_nonneg ((v ⬝ᵥ B *ᵥ x) / 2 - 2 * (μ * (v ⬝ᵥ x)))]
  have hmux : (μ * (v ⬝ᵥ x)) ^ 2 ≤ μ ^ 2 * (v ⬝ᵥ v) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hvx (by positivity)
  have hP : (v ⬝ᵥ A *ᵥ x) ^ 2 ≤ (5 / 4) * (W * q) + 5 * ((d : ℝ) ^ 2 * lam * W) := by
    nlinarith
  -- conclusion
  have hdl : 5 * ((d : ℝ) ^ 2 * lam) ≤ q / 20 := by linarith
  have hP2 : (v ⬝ᵥ A *ᵥ x) ^ 2 ≤ (13 / 10) * q * W := by
    have := mul_le_mul_of_nonneg_right hdl hW0
    linarith
  have hγ : (2 : ℝ) / ((d : ℝ) + 1) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hγ0 : 0 ≤ (2 : ℝ) / ((d : ℝ) + 1) := by positivity
  have hqW : 0 ≤ q * W := mul_nonneg hqpos.le hW0
  show (2 / ((d : ℝ) + 1)) * (v ⬝ᵥ A *ᵥ x) ^ 2 ≤ q * (v ⬝ᵥ A *ᵥ v - μ * (v ⬝ᵥ v))
  have hWe : v ⬝ᵥ A *ᵥ v - μ * (v ⬝ᵥ v) = W := by rw [hW, hB, hBq]
  rw [hWe]
  calc (2 / ((d : ℝ) + 1)) * (v ⬝ᵥ A *ᵥ x) ^ 2
      ≤ (2 / ((d : ℝ) + 1)) * ((13 / 10) * q * W) := mul_le_mul_of_nonneg_left hP2 hγ0
    _ ≤ (2 / 3) * ((13 / 10) * q * W) := by
        apply mul_le_mul_of_nonneg_right hγ; linarith
    _ ≤ q * W := by linarith

theorem FPE_lemma4 {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (x : Fin d → ℝ) (hx : x ⬝ᵥ x ≤ 1)
    (hsmall : lamMin A ≤ 1 / (400 * (d : ℝ) ^ 2) * ε ^ 2)
    (hexplore : ε ^ 2 / 4 < x ⬝ᵥ A *ᵥ x) :
    lamMin A ≤ lamMin (ellipsoidUpdateMatrix A x) := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hq0 : 0 < x ⬝ᵥ A *ᵥ x := by
    have : 0 < ε ^ 2 / 4 := by positivity
    linarith
  have hx0 : x ≠ 0 := by
    intro h; subst h; simp at hq0
  have hPD := FPE_H_posDef hd A hA x hx0
  have hq : 100 * (d : ℝ) ^ 2 * lamMin A < x ⬝ᵥ A *ᵥ x := by
    have h1 : 100 * (d : ℝ) ^ 2 * lamMin A ≤ 100 * (d : ℝ) ^ 2 * (1 / (400 * (d : ℝ) ^ 2) * ε ^ 2) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    have h2 : 100 * (d : ℝ) ^ 2 * (1 / (400 * (d : ℝ) ^ 2) * ε ^ 2) = ε ^ 2 / 4 := by
      field_simp; ring
    linarith
  apply FPE_le_lamMin hd0 _ hPD.isHermitian
  intro v
  rw [FPE_upd_quad A hA.isHermitian x v]
  have hcore := FPE_L4_core hd A hA x hx hq v
  set q := x ⬝ᵥ A *ᵥ x with hqdef
  set lam := lamMin A with hlam
  have hden : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hW : (2 / ((d : ℝ) + 1)) * (q⁻¹ * (v ⬝ᵥ A *ᵥ x) ^ 2) ≤
      v ⬝ᵥ A *ᵥ v - (lam - lam / (d : ℝ) ^ 2) * (v ⬝ᵥ v) := by
    have e : (2 / ((d : ℝ) + 1)) * (q⁻¹ * (v ⬝ᵥ A *ᵥ x) ^ 2) =
        q⁻¹ * ((2 / ((d : ℝ) + 1)) * (v ⬝ᵥ A *ᵥ x) ^ 2) := by ring
    rw [e]
    calc q⁻¹ * ((2 / ((d : ℝ) + 1)) * (v ⬝ᵥ A *ᵥ x) ^ 2)
        ≤ q⁻¹ * (q * (v ⬝ᵥ A *ᵥ v - (lam - lam / (d : ℝ) ^ 2) * (v ⬝ᵥ v))) :=
          mul_le_mul_of_nonneg_left hcore (inv_nonneg.2 hq0.le)
      _ = _ := by field_simp
  have hc0 : 0 ≤ (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) := by positivity
  have h1 := mul_le_mul_of_nonneg_left
    (show v ⬝ᵥ A *ᵥ v - (v ⬝ᵥ A *ᵥ v - (lam - lam / (d : ℝ) ^ 2) * (v ⬝ᵥ v)) ≤
      v ⬝ᵥ A *ᵥ v - (2 / ((d : ℝ) + 1)) * (q⁻¹ * (v ⬝ᵥ A *ᵥ x) ^ 2) by linarith) hc0
  have h2 : (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) *
      (v ⬝ᵥ A *ᵥ v - (v ⬝ᵥ A *ᵥ v - (lam - lam / (d : ℝ) ^ 2) * (v ⬝ᵥ v))) = lam * (v ⬝ᵥ v) := by
    have : (d : ℝ) ^ 2 - 1 ≠ 0 := hden.ne'
    have : (d : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  linarith

theorem solution {d : ℕ} (hd : 2 ≤ d) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hεR : ε ≤ 20 * R * ((d : ℝ) + 1))
    (θ : Fin d → ℝ) (hθ : θ ⬝ᵥ θ ≤ R ^ 2) (x : ℕ → Fin d → ℝ) (hx : ∀ t, x t ⬝ᵥ x t ≤ 1)
    (t : ℕ) :
    ε ^ 2 / (400 * ((d : ℝ) + 1) ^ 2) ≤ lamMin (shape R ε θ x t) := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) + 1 := by linarith
  induction t with
  | zero =>
    have hPD := (FPE_invariant hd hR hε θ hθ x 0).1
    apply FPE_le_lamMin hd0 _ hPD.isHermitian
    intro v
    have hsh : shape R ε θ x 0 = (R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := rfl
    rw [hsh]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    have hm : ε ^ 2 / (400 * ((d : ℝ) + 1) ^ 2) ≤ R ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : ε ^ 2 ≤ (20 * R * ((d : ℝ) + 1)) ^ 2 := by
        apply pow_le_pow_left₀ hε.le hεR
      nlinarith
    exact mul_le_mul_of_nonneg_right hm (FPE_dot_nonneg v)
  | succ t ih =>
    obtain ⟨hPD, _⟩ := FPE_invariant hd hR hε θ hθ x t
    rcases FPE_shape_succ R ε θ x t with ⟨_, h⟩ | ⟨hex, h⟩
    · rw [h]; exact ih
    · rw [h]
      have hq := FPE_explore_q hε θ x t hex
      have hx0 : x t ≠ 0 := by
        intro h0; rw [h0] at hq; simp at hq
        have : 0 < ε ^ 2 / 4 := by positivity
        linarith
      by_cases hbig : 1 / (400 * (d : ℝ) ^ 2) * ε ^ 2 < lamMin (shape R ε θ x t)
      · have h3 := FPE_lemma3 hd _ hPD (x t) hx0
        have hk : ε ^ 2 / (400 * ((d : ℝ) + 1) ^ 2) =
            (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 * (1 / (400 * (d : ℝ) ^ 2) * ε ^ 2) := by
          field_simp
        rw [hk]
        have : (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 * (1 / (400 * (d : ℝ) ^ 2) * ε ^ 2) ≤
            (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 * lamMin (shape R ε θ x t) :=
          mul_le_mul_of_nonneg_left hbig.le (by positivity)
        linarith
      · have hsmall := not_lt.1 hbig
        have h4 := FPE_lemma4 hd hε _ hPD (x t) (hx t) hsmall hq
        linarith
