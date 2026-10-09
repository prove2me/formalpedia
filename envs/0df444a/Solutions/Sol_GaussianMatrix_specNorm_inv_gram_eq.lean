-- Prove2me | solution 1 for GaussianMatrix.specNorm_inv_gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:46:20.232428+00:00
-- url     : https://prove2.me/submissions/3d153017-77df-42df-8e7c-9081da5ca605

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open scoped Matrix.Norms.L2Operator

lemma igram_euclid_norm {n : Type*} [Fintype n] (v : EuclideanSpace ℝ n) :
    ‖v‖ = Real.sqrt (v.ofLp ⬝ᵥ v.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

lemma igram_dot_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- Cauchy–Schwarz for the dot product. -/
lemma igram_dot_le {n : Type*} [Fintype n] (v w : n → ℝ) :
    v ⬝ᵥ w ≤ Real.sqrt (v ⬝ᵥ v) * Real.sqrt (w ⬝ᵥ w) := by
  rw [← Real.sqrt_mul (igram_dot_self_nonneg v)]
  refine le_trans (le_abs_self _) ?_
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  simpa [dotProduct, sq] using h

/-- `xᵀ (A Aᵀ) x = ‖Aᵀ x‖²`. -/
lemma igram_quad {r k : ℕ} (A : Matrix (Fin r) (Fin k) ℝ) (x : Fin r → ℝ) :
    x ⬝ᵥ ((A * Aᵀ) *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

lemma igram_sMin_nonneg {N n : Type*} [Fintype N] [Fintype n] (B : Matrix N n ℝ) :
    0 ≤ sMin B := by
  unfold sMin
  exact Real.iInf_nonneg fun _ => Real.sqrt_nonneg _

/-- Homogeneous form of the definition of `σ_min`: `σ_min(B)² ‖y‖² ≤ ‖B y‖²`. -/
lemma igram_sMin_sq_mul_le {N n : Type*} [Fintype N] [Fintype n] (B : Matrix N n ℝ)
    (y : n → ℝ) : sMin B ^ 2 * (y ⬝ᵥ y) ≤ (B *ᵥ y) ⬝ᵥ (B *ᵥ y) := by
  rcases (igram_dot_self_nonneg y).lt_or_eq with hpos | hz
  · set c := Real.sqrt (y ⬝ᵥ y) with hc_def
    have hc : 0 < c := Real.sqrt_pos.2 hpos
    have hcc : c ^ 2 = y ⬝ᵥ y := Real.sq_sqrt hpos.le
    have hx : (c⁻¹ • y) ⬝ᵥ (c⁻¹ • y) = 1 := by
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← hcc]
      field_simp
    have hbdd : BddBelow (Set.range fun z : {x : n → ℝ // x ⬝ᵥ x = 1} =>
        Real.sqrt ((B *ᵥ z.1) ⬝ᵥ (B *ᵥ z.1))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact Real.sqrt_nonneg _
    have h1 : sMin B ≤ Real.sqrt ((B *ᵥ (c⁻¹ • y)) ⬝ᵥ (B *ᵥ (c⁻¹ • y))) :=
      ciInf_le hbdd ⟨c⁻¹ • y, hx⟩
    have h2 : (B *ᵥ (c⁻¹ • y)) ⬝ᵥ (B *ᵥ (c⁻¹ • y)) = c⁻¹ ^ 2 * ((B *ᵥ y) ⬝ᵥ (B *ᵥ y)) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      ring
    have h0 := igram_sMin_nonneg B
    have h3 : sMin B ^ 2 ≤ c⁻¹ ^ 2 * ((B *ᵥ y) ⬝ᵥ (B *ᵥ y)) := by
      rw [← h2]
      calc sMin B ^ 2 ≤ (Real.sqrt ((B *ᵥ (c⁻¹ • y)) ⬝ᵥ (B *ᵥ (c⁻¹ • y)))) ^ 2 :=
            pow_le_pow_left₀ h0 h1 2
        _ = _ := Real.sq_sqrt (igram_dot_self_nonneg _)
    calc sMin B ^ 2 * (y ⬝ᵥ y) = c ^ 2 * sMin B ^ 2 := by rw [hcc]; ring
      _ ≤ c ^ 2 * (c⁻¹ ^ 2 * ((B *ᵥ y) ⬝ᵥ (B *ᵥ y))) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = (B *ᵥ y) ⬝ᵥ (B *ᵥ y) := by field_simp
  · rw [← hz, mul_zero]
    exact igram_dot_self_nonneg _

/-- For an invertible Gram matrix and a unit vector `x`, `‖(AAᵀ)⁻¹‖ ≥ 1 / ‖Aᵀ x‖²`. -/
lemma igram_inv_lower {r k : ℕ} (A : Matrix (Fin r) (Fin k) ℝ) (hM : IsUnit (A * Aᵀ).det)
    (x : Fin r → ℝ) (hx : x ⬝ᵥ x = 1) :
    0 < (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) ∧ 1 / ((Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x)) ≤ ‖(A * Aᵀ)⁻¹‖ := by
  set M := A * Aᵀ with hM_def
  set q := (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) with hq_def
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hq : 0 < q := by
    rcases (igram_dot_self_nonneg (Aᵀ *ᵥ x)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : Aᵀ *ᵥ x = 0 := dotProduct_self_eq_zero.1 h.symm
      have h1 : M *ᵥ x = 0 := by rw [hM_def, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      have h2 : x = 0 := by
        have : M⁻¹ *ᵥ (M *ᵥ x) = x := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
        rw [← this, h1, Matrix.mulVec_zero]
      rw [h2, dotProduct_zero] at hx
      exact zero_ne_one hx
  refine ⟨hq, ?_⟩
  set w := M⁻¹ *ᵥ x with hw_def
  have hMw : M *ᵥ w = x := by rw [hw_def, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have hsym : Mᵀ = M := by rw [hM_def, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hwMx : w ⬝ᵥ (M *ᵥ x) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hMw, hx]
  have hxMx : x ⬝ᵥ (M *ᵥ x) = q := igram_quad A x
  set c := 1 / q with hc_def
  have hpsd : 0 ≤ (w - c • x) ⬝ᵥ (M *ᵥ (w - c • x)) := by
    rw [hM_def, igram_quad]; exact igram_dot_self_nonneg _
  have hexp : (w - c • x) ⬝ᵥ (M *ᵥ (w - c • x)) = w ⬝ᵥ x - 1 / q := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMw, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul, hwMx, hxMx, hx, dotProduct_smul]
    rw [hc_def]
    field_simp
    ring
  have hwx : 1 / q ≤ w ⬝ᵥ x := by linarith
  have hCS : w ⬝ᵥ x ≤ Real.sqrt (w ⬝ᵥ w) := by
    have := igram_dot_le w x
    rwa [hx, Real.sqrt_one, mul_one] at this
  have hop : Real.sqrt (w ⬝ᵥ w) ≤ ‖M⁻¹‖ := by
    have h := Matrix.l2_opNorm_mulVec M⁻¹ (WithLp.toLp 2 x)
    rw [igram_euclid_norm, igram_euclid_norm] at h
    have h' : Real.sqrt (w ⬝ᵥ w) ≤ ‖M⁻¹‖ * Real.sqrt (x ⬝ᵥ x) := h
    rwa [hx, Real.sqrt_one, mul_one] at h'
  linarith

/-- If `σ_min(Aᵀ) > 0` then `AAᵀ` is invertible and `‖(AAᵀ)⁻¹‖ ≤ 1/σ_min(Aᵀ)²`. -/
lemma igram_inv_upper {r k : ℕ} (A : Matrix (Fin r) (Fin k) ℝ) (hs : 0 < sMin Aᵀ) :
    IsUnit (A * Aᵀ).det ∧ ‖(A * Aᵀ)⁻¹‖ ≤ 1 / sMin Aᵀ ^ 2 := by
  set M := A * Aᵀ with hM_def
  set s := sMin Aᵀ with hs_def
  have hs2 : 0 < s ^ 2 := by positivity
  have hlow : ∀ y : Fin r → ℝ, s ^ 2 * (y ⬝ᵥ y) ≤ y ⬝ᵥ (M *ᵥ y) := fun y => by
    rw [hM_def, igram_quad]; exact igram_sMin_sq_mul_le Aᵀ y
  have hunit : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have h1 := hlow v
    rw [hv, dotProduct_zero] at h1
    have h2 : v ⬝ᵥ v = 0 := le_antisymm (by nlinarith [igram_dot_self_nonneg v])
      (igram_dot_self_nonneg v)
    exact hv0 (dotProduct_self_eq_zero.1 h2)
  refine ⟨hunit, ?_⟩
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  show ‖(Matrix.toEuclideanLin M⁻¹ y)‖ ≤ 1 / s ^ 2 * ‖y‖
  rw [igram_euclid_norm, igram_euclid_norm]
  have hT : (Matrix.toEuclideanLin M⁻¹ y).ofLp = M⁻¹ *ᵥ y.ofLp := rfl
  rw [hT]
  set w := M⁻¹ *ᵥ y.ofLp with hw_def
  set yy := y.ofLp with hyy
  have hMw : M *ᵥ w = yy := by rw [hw_def, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have h1 := hlow w
  rw [hMw] at h1
  have h2 := igram_dot_le w yy
  set a := Real.sqrt (w ⬝ᵥ w)
  set b := Real.sqrt (yy ⬝ᵥ yy)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have haa : a ^ 2 = w ⬝ᵥ w := Real.sq_sqrt (igram_dot_self_nonneg _)
  -- `s² a² ≤ a b`, hence `s² a ≤ b`
  have h3 : s ^ 2 * a ^ 2 ≤ a * b := by rw [haa]; linarith
  have h4 : s ^ 2 * a ≤ b := by
    rcases ha.lt_or_eq with hapos | ha0
    · nlinarith
    · rw [← ha0, mul_zero]; exact hb
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs2]
  linarith

end GaussianMatrix

open GaussianMatrix

open scoped Matrix.Norms.L2Operator in
theorem solution {r k : ℕ} (A : Matrix (Fin r) (Fin k) ℝ) :
    specNorm (A * Aᵀ)⁻¹ = 1 / sMin Aᵀ ^ 2 := by
  unfold specNorm
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have h1 : (A * Aᵀ)⁻¹ = 0 := Subsingleton.elim _ _
    have h2 : sMin Aᵀ = 0 := by
      unfold sMin
      have : IsEmpty {x : Fin 0 → ℝ // x ⬝ᵥ x = 1} :=
        ⟨fun x => by have := x.2; simp [dotProduct] at this⟩
      exact Real.iInf_of_isEmpty _
    rw [h1, h2, norm_zero]; simp
  · by_cases hM : IsUnit (A * Aᵀ).det
    · have hne : Nonempty {x : Fin r → ℝ // x ⬝ᵥ x = 1} :=
        ⟨⟨Pi.single ⟨0, hr⟩ 1, by simp⟩⟩
      set N := ‖(A * Aᵀ)⁻¹‖ with hN_def
      have x0 := hne.some
      have hNpos : 0 < N := by
        obtain ⟨hq, hle⟩ := igram_inv_lower A hM x0.1 x0.2
        exact lt_of_lt_of_le (by positivity) hle
      have hlow : 1 / Real.sqrt N ≤ sMin Aᵀ := by
        unfold sMin
        refine le_ciInf fun x => ?_
        obtain ⟨hq, hle⟩ := igram_inv_lower A hM x.1 x.2
        have h1 : 1 / N ≤ (Aᵀ *ᵥ x.1) ⬝ᵥ (Aᵀ *ᵥ x.1) := by
          rw [div_le_iff₀ hNpos]; rw [div_le_iff₀ hq] at hle; linarith
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_div' _ hNpos.le, Real.sqrt_one] at h2
      have hs : 0 < sMin Aᵀ := lt_of_lt_of_le (by positivity) hlow
      have hup := (igram_inv_upper A hs).2
      apply le_antisymm hup
      have h1 : 1 / N ≤ sMin Aᵀ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hlow 2
        rwa [div_pow, one_pow, Real.sq_sqrt hNpos.le] at this
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hNpos] at h1
      linarith
    · have h1 : (A * Aᵀ)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hM
      have h2 : sMin Aᵀ = 0 := by
        rcases (igram_sMin_nonneg Aᵀ).lt_or_eq with h | h
        · exact absurd (igram_inv_upper A h).1 hM
        · exact h.symm
      rw [h1, h2, norm_zero]; simp
