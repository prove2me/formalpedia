-- Prove2me | solution 1 for FeaturePricing.Ellipsoid.lemma2_rank_one_min_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:00:55.53469+00:00
-- url     : https://prove2.me/submissions/9a425514-367e-416a-986d-dafac508dd95

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

theorem solution {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (b : Fin d → ℝ) (β : ℝ) (hβ : 0 < β) (z : ℝ) (hz : z < lamMin A)
    (hφ : 0 ≤ (A - β • vecMulVec b b - z • (1 : Matrix (Fin d) (Fin d) ℝ)).det) :
    z ≤ lamMin (A - β • vecMulVec b b) := by
  set C : Matrix (Fin d) (Fin d) ℝ := A - z • (1 : Matrix (Fin d) (Fin d) ℝ) with hC
  have hCh : C.IsHermitian := FPE_herm_shift A hA z
  have hCq : ∀ v : Fin d → ℝ, (lamMin A - z) * (v ⬝ᵥ v) ≤ v ⬝ᵥ C *ᵥ v := by
    intro v
    have := FPE_lamMin_le_quad hd A hA v
    rw [hC]
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    linarith
  have hCpd : C.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hCh ?_
    intro v hv
    have h1 : 0 < v ⬝ᵥ v := by
      rcases lt_or_eq_of_le (FPE_dot_nonneg v) with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.1 h.symm) hv
    have := hCq v
    simp only [star_trivial]
    nlinarith
  have hCinv : C⁻¹.PosDef := hCpd.inv
  have hdet : 0 < C.det := hCpd.det_pos
  -- determinant factorisation
  have hfac : C - β • vecMulVec b b = C * (1 - β • vecMulVec (C⁻¹ *ᵥ b) b) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hCpd.isUnit),
      Matrix.one_mulVec]
  have hdet2 : (C - β • vecMulVec b b).det = C.det * (1 - β * (b ⬝ᵥ C⁻¹ *ᵥ b)) := by
    rw [hfac, Matrix.det_mul, det_one_sub_vecMulVec]
  have hφ' : 0 ≤ (C - β • vecMulVec b b).det := by
    have : A - β • vecMulVec b b - z • (1 : Matrix (Fin d) (Fin d) ℝ) = C - β • vecMulVec b b := by
      rw [hC]; abel
    rw [← this]; exact hφ
  have hβb : β * (b ⬝ᵥ C⁻¹ *ᵥ b) ≤ 1 := by
    rw [hdet2] at hφ'
    have := nonneg_of_mul_nonneg_right hφ' hdet
    linarith
  -- Hermitian
  have hDh : (A - β • vecMulVec b b).IsHermitian := by
    unfold Matrix.IsHermitian at *
    rw [Matrix.conjTranspose_sub, hA, Matrix.conjTranspose_smul]
    have : (vecMulVec b b : Matrix (Fin d) (Fin d) ℝ)ᴴ = vecMulVec b b := by
      ext i j; simp [vecMulVec, mul_comm]
    rw [this]; simp
  apply FPE_le_lamMin hd _ hDh
  intro v
  have hcs := FPE_cs C⁻¹ hCinv.posSemidef (C *ᵥ v) b
  rw [FPE_inv_mulVec C hCpd v] at hcs
  have e1 : (C *ᵥ v) ⬝ᵥ (C⁻¹ *ᵥ b) = v ⬝ᵥ b := by
    rw [dotProduct_comm, FPE_symm C hCh, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hCpd.isUnit), Matrix.one_mulVec]
  have e2 : (C *ᵥ v) ⬝ᵥ v = v ⬝ᵥ C *ᵥ v := dotProduct_comm _ _
  rw [e1, e2] at hcs
  have hquad : v ⬝ᵥ (A - β • vecMulVec b b) *ᵥ v = v ⬝ᵥ A *ᵥ v - β * (v ⬝ᵥ b) ^ 2 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      Matrix.vecMulVec_mulVec, smul_eq_mul, op_smul_eq_smul]
    rw [dotProduct_comm b v]
    ring
  have hCv : v ⬝ᵥ C *ᵥ v = v ⬝ᵥ A *ᵥ v - z * (v ⬝ᵥ v) := by
    rw [hC]
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  have hCv0 : 0 ≤ v ⬝ᵥ C *ᵥ v := hCpd.posSemidef.dotProduct_mulVec_nonneg v
  have hstep : β * (v ⬝ᵥ b) ^ 2 ≤ v ⬝ᵥ C *ᵥ v := by
    calc β * (v ⬝ᵥ b) ^ 2 ≤ β * ((v ⬝ᵥ C *ᵥ v) * (b ⬝ᵥ C⁻¹ *ᵥ b)) :=
          mul_le_mul_of_nonneg_left hcs hβ.le
      _ = (v ⬝ᵥ C *ᵥ v) * (β * (b ⬝ᵥ C⁻¹ *ᵥ b)) := by ring
      _ ≤ (v ⬝ᵥ C *ᵥ v) * 1 := mul_le_mul_of_nonneg_left hβb hCv0
      _ = _ := mul_one _
  rw [hquad]
  linarith
