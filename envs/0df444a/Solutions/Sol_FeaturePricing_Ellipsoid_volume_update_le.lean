-- Prove2me | solution 1 for FeaturePricing.Ellipsoid.volume_update_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:46:33.173194+00:00
-- url     : https://prove2.me/submissions/5f9ea753-ef61-472b-afa0-c7145297f90f

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

/-- The scalar volume-ratio estimate `(d²/(d²-1))^d (d-1)/(d+1) ≤ e^{-1/d}`. -/
theorem FPE_R_le {n : ℕ} (hn : 2 ≤ n) :
    (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n) * (((n : ℝ) - 1) / ((n : ℝ) + 1)) ≤
      Real.exp (-1 / (n : ℝ)) := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have : n = 2 := by omega
    subst this
    norm_num
    -- goal: 16/27 ≤ exp (-1/2)
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp (1 / 2) < 27 / 16 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [Real.exp_pos (1 / 2)]
    have h4 : Real.exp (-(1 / 2)) = (Real.exp (1 / 2))⁻¹ := by
      rw [Real.exp_neg]
    rw [h4]
    have hp := Real.exp_pos (1 / 2)
    rw [le_inv_comm₀ (by norm_num) hp]
    linarith
  · set N : ℝ := (n : ℝ) with hN
    have hN3 : (3 : ℝ) ≤ N := by rw [hN]; exact_mod_cast h3
    have hN0 : 0 < N := by linarith
    set x : ℝ := 1 / N with hx
    have hx0 : 0 < x := by positivity
    have hx3 : x ≤ 1 / 3 := by
      rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hN3
    have hx1 : x < 1 := by linarith
    have hxN : N * x = 1 := by rw [hx]; field_simp
    have hxx : x * x < 1 := by nlinarith
    have hα : N ^ 2 / (N ^ 2 - 1) = (1 - x ^ 2)⁻¹ := by
      have hNsq : N ^ 2 - 1 ≠ 0 := by nlinarith
      have : 1 - x ^ 2 = (N ^ 2 - 1) / N ^ 2 := by
        rw [hx]; field_simp
      rw [this, inv_div]
    have hr : (N - 1) / (N + 1) = ((1 + x) / (1 - x))⁻¹ := by
      rw [hx]
      have : N + 1 ≠ 0 := by linarith
      have : N - 1 ≠ 0 := by linarith
      field_simp
    rw [hα, hr]
    have h1x2 : 0 < 1 - x ^ 2 := by nlinarith
    have hRpos : 0 < ((1 - x ^ 2)⁻¹) ^ n * ((1 + x) / (1 - x))⁻¹ := by
      have : 0 < 1 - x := by linarith
      positivity
    have h1x : 0 < 1 - x := by linarith
    have h1px : 0 < 1 + x := by linarith
    have hq : 0 < (1 + x) / (1 - x) := by positivity
    refine (Real.log_le_iff_le_exp hRpos).1 ?_
    rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero h1x2.ne')) (inv_ne_zero hq.ne'),
      Real.log_pow, Real.log_inv, Real.log_inv]
    -- upper bound for -log(1 - x^2)
    have hy : |x ^ 2| < 1 := by rw [abs_of_nonneg (by positivity)]; nlinarith
    have hA := Real.abs_log_sub_add_sum_range_le hy 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hA
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2)] at hA
    have hA' := (abs_le.1 hA).1
    norm_num at hA'
    -- lower bound for log((1+x)/(1-x))
    have hB := Real.sum_range_le_log_div hx0.le hx1 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hB
    norm_num at hB
    -- the tail term
    have htail : (x ^ 2) ^ 3 / (1 - x ^ 2) ≤ x ^ 4 / 6 := by
      rw [div_le_iff₀ h1x2]
      have : x ^ 2 ≤ 1 / 9 := by nlinarith
      have h4 : 0 ≤ x ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h4]
    have hlogA : -Real.log (1 - x ^ 2) ≤ x ^ 2 + (x ^ 2) ^ 2 / 2 + x ^ 4 / 6 := by
      have : (x ^ 2) ^ 3 / (1 - x ^ 2) ≤ x ^ 4 / 6 := htail
      nlinarith [hA']
    have hn' : (n : ℝ) = N := hN.symm
    rw [hn']
    have hmul := mul_le_mul_of_nonneg_left hlogA hN0.le
    have e1 : N * (x ^ 2 + (x ^ 2) ^ 2 / 2 + x ^ 4 / 6) = x + x ^ 3 / 2 + x ^ 3 / 6 := by
      have : N * x = 1 := hxN
      have h2 : N * x ^ 2 = x := by nlinarith
      have h3 : N * (x ^ 2) ^ 2 = x ^ 3 := by
        have : (x ^ 2) ^ 2 = x ^ 3 * x := by ring
        rw [this, ← mul_assoc, mul_comm N, mul_assoc, hxN]; ring
      have h4 : N * x ^ 4 = x ^ 3 := by
        have : x ^ 4 = x ^ 3 * x := by ring
        rw [this, ← mul_assoc, mul_comm N, mul_assoc, hxN]; ring
      calc N * (x ^ 2 + (x ^ 2) ^ 2 / 2 + x ^ 4 / 6)
          = N * x ^ 2 + (N * (x ^ 2) ^ 2) / 2 + (N * x ^ 4) / 6 := by ring
        _ = _ := by rw [h2, h3, h4]
    have : -1 / N = -x := by rw [hx]; ring
    rw [this]
    have hx3' : 0 < x ^ 3 := by positivity
    nlinarith [hmul, hB, e1]

theorem solution {d : ℕ} (hd : 2 ≤ d) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (x : Fin d → ℝ) (hx : x ≠ 0) (c c' : Fin d → ℝ) :
    volume (ellipsoid c' (ellipsoidUpdateMatrix A x)) ≤
      ENNReal.ofReal (Real.exp (-1 / (2 * (d : ℝ)))) * volume (ellipsoid c A) := by
  have hDbar : (ellipsoidUpdateMatrix A x).PosDef := FPE_H_posDef hd A hA x hx
  rw [ellipsoid_volume_formula c' _ hDbar, ellipsoid_volume_formula c A hA,
    ellipsoid_update_det hd A hA x hx]
  set Rr : ℝ := (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d) * (((d : ℝ) - 1) / ((d : ℝ) + 1)) with hRr
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hRpos : 0 ≤ Rr := by
    have hden : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
    rw [hRr]
    have : 0 < ((d : ℝ) - 1) / ((d : ℝ) + 1) := div_pos (by linarith) (by linarith)
    positivity
  have hs : Real.sqrt Rr ≤ Real.exp (-1 / (2 * (d : ℝ))) := by
    rw [Real.sqrt_le_iff]
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have h1 := FPE_R_le hd
    have h2 : Real.exp (-1 / (2 * (d : ℝ))) ^ 2 = Real.exp (-1 / (d : ℝ)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [h2]; exact h1
  rw [Real.sqrt_mul hRpos, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  calc ENNReal.ofReal (Real.sqrt Rr) * ENNReal.ofReal (Real.sqrt A.det) * volume (quadBall d)
      ≤ ENNReal.ofReal (Real.exp (-1 / (2 * (d : ℝ)))) * ENNReal.ofReal (Real.sqrt A.det) *
          volume (quadBall d) := by
        gcongr
    _ = _ := by ring
