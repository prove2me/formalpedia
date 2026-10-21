-- Prove2me | solution 1 for FeaturePricing.Ellipsoid.lemma4_min_eigenvalue_no_decrease
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:59:15.022269+00:00
-- url     : https://prove2.me/submissions/bc1464db-5e4d-4364-8fc3-85e1ab1f51e9

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

theorem solution {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
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
