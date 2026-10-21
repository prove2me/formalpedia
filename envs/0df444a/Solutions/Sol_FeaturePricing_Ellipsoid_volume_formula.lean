-- Prove2me | solution 1 for FeaturePricing.Ellipsoid.volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:42:12.396842+00:00
-- url     : https://prove2.me/submissions/572fa61a-bbe2-422d-b034-93179d2b418d

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing

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


theorem FPE_det_eigs {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) :
    A.det = ∏ i, hA.isHermitian.eigenvalues i := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  simp

theorem solution {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) :
    volume (ellipsoid a A) =
      volume (ellipsoidBall (0 : Fin d → ℝ) 1) *
        ENNReal.ofReal (Real.sqrt (∏ i, hA.isHermitian.eigenvalues i)) := by
  have h1 := ellipsoid_volume_formula a A hA
  have hI : ((1 : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := by
    simpa using (Matrix.PosDef.one : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef)
  have h2 := ellipsoid_volume_formula (0 : Fin d → ℝ) _ hI
  have hb : volume (ellipsoidBall (0 : Fin d → ℝ) 1) = volume (quadBall d) := by
    unfold ellipsoidBall
    rw [h2]
    simp
  rw [hb, h1, FPE_det_eigs A hA, mul_comm]
