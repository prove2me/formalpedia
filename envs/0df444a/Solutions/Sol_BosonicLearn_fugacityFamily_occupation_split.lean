-- Prove2me | solution 1 for BosonicLearn.fugacityFamily_occupation_split
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:02:20.504544+00:00
-- url     : https://prove2.me/submissions/7b833ecd-61b1-49c2-ac3f-664b46317b06

import Mathlib
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp

open scoped ENNReal Matrix ComplexOrder
open BosonicLearn

noncomputable section

private lemma rsmul_herm {n : ℕ} (c : ℝ) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (((c : ℝ) : ℂ) • A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA.eq]
  simp

/-- Inversion is antitone for the Loewner order: `A ⪯ αB ⇒ B⁻¹ ⪯ αA⁻¹`. -/
private lemma inv_anti {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (α : ℝ) (hα : 0 < α) (hAB : (((α : ℝ) : ℂ) • B - A).PosSemidef) :
    (((α : ℝ) : ℂ) • A⁻¹ - B⁻¹).PosSemidef := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hAh : Aᴴ = A := hA.isHermitian.eq
  have hBh : Bᴴ = B := hB.isHermitian.eq
  have hAih : (A⁻¹)ᴴ = A⁻¹ := hA.isHermitian.inv.eq
  have hBih : (B⁻¹)ᴴ = B⁻¹ := hB.isHermitian.inv.eq
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((rsmul_herm α hA.isHermitian.inv).sub hB.isHermitian.inv) fun v => ?_
  set x : Fin n → ℂ := A⁻¹ *ᵥ v with hx
  set y : Fin n → ℂ := B⁻¹ *ᵥ v with hy
  have hAx : A *ᵥ x = v := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAdet, Matrix.one_mulVec]
  have hBy : B *ᵥ y = v := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hBdet, Matrix.one_mulVec]
  set P : ℂ := star v ⬝ᵥ x with hP
  set Q : ℂ := star v ⬝ᵥ y with hQ
  set S : ℂ := star y ⬝ᵥ (A *ᵥ y) with hS
  have h1 : star x ⬝ᵥ v = P := by
    rw [hP, hx, Matrix.star_mulVec, hAih, ← Matrix.dotProduct_mulVec]
  have h2 : star y ⬝ᵥ v = Q := by
    rw [hQ, hy, Matrix.star_mulVec, hBih, ← Matrix.dotProduct_mulVec]
  have h3 : star x ⬝ᵥ (A *ᵥ y) = Q := by
    rw [Matrix.dotProduct_mulVec, ← hAh, ← Matrix.star_mulVec, hAx]
  have hpos := hA.posSemidef.dotProduct_mulVec_nonneg (x - ((α⁻¹ : ℝ) : ℂ) • y)
  have hexp : star (x - ((α⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ (A *ᵥ (x - ((α⁻¹ : ℝ) : ℂ) • y)) =
      P - ((α⁻¹ : ℝ) : ℂ) * Q - ((α⁻¹ : ℝ) : ℂ) * Q + ((α⁻¹ : ℝ) : ℂ) * ((α⁻¹ : ℝ) : ℂ) * S := by
    have hs : star (x - ((α⁻¹ : ℝ) : ℂ) • y) = star x - ((α⁻¹ : ℝ) : ℂ) • star y := by
      funext i
      simp
    rw [hs]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hAx, h1, h2, h3, ← hS]
    ring
  rw [hexp] at hpos
  have hcmp := hAB.dotProduct_mulVec_nonneg y
  have hcmp' : star y ⬝ᵥ ((((α : ℝ) : ℂ) • B - A) *ᵥ y) = ((α : ℝ) : ℂ) * Q - S := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hBy, h2]
  rw [hcmp'] at hcmp
  have hci : (0 : ℂ) ≤ ((α⁻¹ : ℝ) : ℂ) * ((α⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    exact Complex.zero_le_real.mpr (by positivity)
  have hsum := add_nonneg hpos (mul_nonneg hci hcmp)
  have hcc : ((α⁻¹ : ℝ) : ℂ) * ((α : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hα.ne']
    simp
  have hα0 : (0 : ℂ) ≤ ((α : ℝ) : ℂ) := Complex.zero_le_real.mpr hα.le
  have hfin : star v ⬝ᵥ ((((α : ℝ) : ℂ) • A⁻¹ - B⁻¹) *ᵥ v) =
      ((α : ℝ) : ℂ) * (P - ((α⁻¹ : ℝ) : ℂ) * Q - ((α⁻¹ : ℝ) : ℂ) * Q +
        ((α⁻¹ : ℝ) : ℂ) * ((α⁻¹ : ℝ) : ℂ) * S +
        ((α⁻¹ : ℝ) : ℂ) * ((α⁻¹ : ℝ) : ℂ) * (((α : ℝ) : ℂ) * Q - S)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      ← hx, ← hy, ← hP, ← hQ]
    linear_combination (-(Q * (((α⁻¹ : ℝ) : ℂ) * ((α : ℝ) : ℂ) - 1))) * hcc
  rw [hfin]
  exact mul_nonneg hα0 hsum

/-- `-c ⪯ A ⪯ c ⇒ A² ⪯ c²`. -/
private lemma loewner_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (hc : 0 < c) (h1 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A).PosSemidef)
    (h2 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A).PosSemidef) :
    (((c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A * A).PosSemidef := by
  have e1 := h2.mul_mul_conjTranspose_same (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A)
  have e2 := h1.mul_mul_conjTranspose_same (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A)
  rw [h1.isHermitian.eq] at e1
  rw [h2.isHermitian.eq] at e2
  have key : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) *
            (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A) *
            (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) +
          (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A) *
            (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) *
            (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A) =
      ((2 * c : ℝ) : ℂ) • (((c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A * A) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_sub, smul_add, smul_smul]
    push_cast
    module
  have hcc : (((2 * c)⁻¹ : ℝ) : ℂ) * ((2 * c : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity)]
    simp
  have key2 : ((c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A * A =
      (((2 * c)⁻¹ : ℝ) : ℂ) • (((2 * c : ℝ) : ℂ) •
        (((c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A * A)) := by
    rw [smul_smul, hcc, one_smul]
  rw [key2, ← key]
  exact (e1.add e2).smul (Complex.zero_le_real.mpr (by positivity))

/-- Unitary diagonalization of a Hermitian matrix, in the form `U D Uᴴ = diag(e)`. -/
private lemma diag_data {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      U * D * Uᴴ = Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hD.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  have hspec : D = V * Matrix.diagonal (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    have h := hD.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  refine ⟨Vᴴ, hD.eigenvalues, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose]; exact hV2
  · rw [Matrix.conjTranspose_conjTranspose]; exact hV1
  · rw [Matrix.conjTranspose_conjTranspose]
    conv_lhs => rw [hspec]
    have h : Vᴴ * (V * Matrix.diagonal (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) * Vᴴ) * V =
        (Vᴴ * V) * Matrix.diagonal (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    rw [h, hV1, Matrix.one_mul, Matrix.mul_one]

/-- The trace norm of a Hermitian matrix is attained on a unitary: `‖H‖₁ = Tr(H W)`. -/
private lemma schatten_one_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, Wᴴ * W = 1 ∧
      WHMultiplicativity.schattenNorm 1 H = (H * W).trace.re := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  set x : Fin n → ℝ := hH.eigenvalues with hx
  have hspec : H = V * Matrix.diagonal (fun i => ((x i : ℝ) : ℂ)) * Vᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  have hcfc : cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) =
      V * Matrix.diagonal (fun i => ((|x i| : ℝ) : ℂ)) * Vᴴ := by
    rw [hH.eq]
    have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
    have h1 : H * H = cfc (fun t : ℝ => t ^ 2) H := by
      rw [cfc_pow_id H 2, pow_two]
    have hc : Continuous (fun t : ℝ => t ^ ((1 : ℝ) / 2)) :=
      Real.continuous_rpow_const (by norm_num)
    rw [h1, ← cfc_comp' (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (fun t : ℝ => t ^ 2) H hc.continuousOn,
      hH.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, ← hVdef, Matrix.star_eq_conjTranspose]
    have hd : (RCLike.ofReal ∘ (fun t : ℝ => (t ^ 2) ^ ((1 : ℝ) / 2)) ∘ hH.eigenvalues :
        Fin n → ℂ) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      simp only [Function.comp_apply]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rfl
    rw [hd]
  have hnorm : WHMultiplicativity.schattenNorm 1 H =
      (cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H)).trace.re := by
    unfold WHMultiplicativity.schattenNorm
    rw [if_neg ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, div_one]
    rw [Real.rpow_one]
  set s : Fin n → ℝ := fun i => if 0 ≤ x i then 1 else -1 with hs
  have hss : ∀ i, s i * s i = 1 := by
    intro i
    simp only [hs]
    split_ifs <;> norm_num
  have hxs : ∀ i, x i * s i = |x i| := by
    intro i
    simp only [hs]
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set W : Matrix (Fin n) (Fin n) ℂ := V * Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) * Vᴴ with hW
  have hWh : Wᴴ = W := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext i
    simp
  have hmul : ∀ d₁ d₂ : Fin n → ℂ, (V * Matrix.diagonal d₁ * Vᴴ) * (V * Matrix.diagonal d₂ * Vᴴ) =
      V * Matrix.diagonal (fun i => d₁ i * d₂ i) * Vᴴ := by
    intro d₁ d₂
    have h : (V * Matrix.diagonal d₁ * Vᴴ) * (V * Matrix.diagonal d₂ * Vᴴ) =
        V * (Matrix.diagonal d₁ * (Vᴴ * V) * Matrix.diagonal d₂) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    rw [h, hV1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  refine ⟨W, ?_, ?_⟩
  · rw [hWh, hW, hmul]
    have h1 : (fun i => ((s i : ℝ) : ℂ) * ((s i : ℝ) : ℂ)) = fun _ : Fin n => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hss i, Complex.ofReal_one]
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, hV2]
  · rw [hnorm, hcfc]
    have h2 : (fun i => ((x i : ℝ) : ℂ) * ((s i : ℝ) : ℂ)) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hxs i]
    conv_rhs => rw [hspec, hW, hmul, h2]

/-- Hölder-type bound: `|Tr(diag(e) P Q)| ≤ ∑ |eᵢ|` when `P Pᴴ ⪯ 1` and `Qᴴ Q ⪯ 1`. -/
private lemma holder {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ)
    (hP : (1 - P * Pᴴ).PosSemidef) (hQ : (1 - Qᴴ * Q).PosSemidef) :
    |(Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (P * Q)).trace.re| ≤ ∑ i, |e i| := by
  have hProw : ∀ i, ∑ j, ‖P i j‖ ^ 2 ≤ 1 := by
    intro i
    have h := hP.diag_nonneg (i := i)
    have h2 : (1 - P * Pᴴ) i i = ((1 - ∑ j, ‖P i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']
    rw [h2] at h
    have := Complex.zero_le_real.mp h
    linarith
  have hQcol : ∀ i, ∑ j, ‖Q j i‖ ^ 2 ≤ 1 := by
    intro i
    have h := hQ.diag_nonneg (i := i)
    have h2 : (1 - Qᴴ * Q) i i = ((1 - ∑ j, ‖Q j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
    rw [h2] at h
    have := Complex.zero_le_real.mp h
    linarith
  have htr : (Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (P * Q)).trace.re =
      ∑ i, e i * ∑ j, (P i j * Q j i).re := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.diagonal_mul]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply, Complex.re_ofReal_mul, Complex.re_sum]
  rw [htr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hone : |∑ j, (P i j * Q j i).re| ≤ 1 := by
    calc |∑ j, (P i j * Q j i).re| ≤ ∑ j, |(P i j * Q j i).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (‖P i j‖ ^ 2 + ‖Q j i‖ ^ 2) / 2 := Finset.sum_le_sum fun j _ => by
          have h1 : |(P i j * Q j i).re| ≤ ‖P i j‖ * ‖Q j i‖ := by
            rw [← norm_mul]
            exact Complex.abs_re_le_norm _
          nlinarith [sq_nonneg (‖P i j‖ - ‖Q j i‖)]
      _ = (∑ j, ‖P i j‖ ^ 2 + ∑ j, ‖Q j i‖ ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ 1 := by linarith [hProw i, hQcol i]
  calc |e i| * |∑ j, (P i j * Q j i).re| ≤ |e i| * 1 :=
        mul_le_mul_of_nonneg_left hone (abs_nonneg _)
    _ = |e i| := mul_one _

/-- The coordinate projector onto the modes in `A`. -/
private abbrev proj {n : ℕ} (A : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)

private lemma proj_conj {n : ℕ} (A : Finset (Fin n)) : (proj A)ᴴ = proj A := by
  rw [proj, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply]
  split_ifs <;> simp

private lemma proj_mul {n : ℕ} (A : Finset (Fin n)) : proj A * proj A = proj A := by
  rw [proj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

private lemma proj_trace {n : ℕ} (A : Finset (Fin n)) : (proj A).trace = (A.card : ℂ) := by
  rw [proj, Matrix.trace_diagonal]
  simp

private lemma proj_compress {n : ℕ} (A : Finset (Fin n)) {K : Matrix (Fin n) (Fin n) ℂ}
    (hK : K.PosSemidef) : (proj A * K * proj A).PosSemidef := by
  have h := hK.mul_mul_conjTranspose_same (proj A)
  rwa [proj_conj] at h

private lemma proj_smul {n : ℕ} (A : Finset (Fin n)) (c : ℂ) :
    proj A * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * proj A = c • proj A := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, proj_mul]

/-- The compressions: all conclusions of the theorem in terms of `Y± = U N± Uᴴ`. -/
private lemma core {n : ℕ} (Yp Ym : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ) (A : Finset (Fin n))
    (ν c' : ℝ) (hν : 0 ≤ ν) (hc' : 0 < c')
    (hdiff : Yp - Ym = Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)))
    (hA : ∀ i ∈ A, 0 ≤ e i)
    (hlow : (Ym - ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hupm : (((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Ym).PosSemidef)
    (hupp : (((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Yp).PosSemidef) :
    (proj A * Ym * proj A).PosSemidef ∧
    (proj A * Yp * proj A - proj A * Ym * proj A).PosSemidef ∧
    (∀ C : ℝ, c' ≤ C →
      (((C : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - proj A * Yp * proj A).PosSemidef) ∧
    (proj A * Yp * proj A - proj A * Ym * proj A).trace.re = ∑ i ∈ A, e i ∧
    ν * A.card ≤ (proj A * Ym * proj A).trace.re ∧
    (proj A * Ym * proj A + proj A * Ym * proj A * (proj A * Ym * proj A)).trace.re ≤
      (c' + c' ^ 2) * A.card := by
  have hYm : Ym.PosSemidef := by
    have e : Ym = (Ym - ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [sub_add_cancel]
    rw [e]
    exact hlow.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hν))
  have hdiag : proj A * Yp * proj A - proj A * Ym * proj A =
      Matrix.diagonal (fun i => ((if i ∈ A then e i else 0 : ℝ) : ℂ)) := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, hdiff, proj, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  -- trace bounds through compressions
  have htr_up : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (c : ℝ),
      (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Z).PosSemidef →
      (proj A * Z * proj A).trace.re ≤ c * A.card := by
    intro Z c hZ
    have h := (proj_compress A hZ).trace_nonneg
    rw [Matrix.mul_sub, Matrix.sub_mul, proj_smul, Matrix.trace_sub, Matrix.trace_smul,
      proj_trace] at h
    have h' := (Complex.nonneg_iff.mp h).1
    simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] at h'
    linarith
  refine ⟨proj_compress A hYm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdiag, Matrix.posSemidef_diagonal_iff]
    intro i
    refine Complex.zero_le_real.mpr ?_
    split_ifs with h
    · exact hA i h
    · exact le_rfl
  · intro C hC
    have hd : Matrix.diagonal (fun i => ((C - (if i ∈ A then c' else 0) : ℝ) : ℂ)) =
        ((C : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - ((c' : ℝ) : ℂ) • proj A := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one]
        split_ifs <;> simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have e : ((C : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - proj A * Yp * proj A =
        proj A * (((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Yp) * proj A +
          Matrix.diagonal (fun i => ((C - (if i ∈ A then c' else 0) : ℝ) : ℂ)) := by
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, proj_smul]
      abel
    rw [e]
    refine (proj_compress A hupp).add ?_
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    refine Complex.zero_le_real.mpr ?_
    split_ifs <;> linarith
  · rw [hdiag, Matrix.trace_diagonal, Complex.re_sum]
    simp only [Complex.ofReal_re]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  · have h := (proj_compress A hlow).trace_nonneg
    rw [Matrix.mul_sub, Matrix.sub_mul, proj_smul, Matrix.trace_sub, Matrix.trace_smul,
      proj_trace] at h
    have h' := (Complex.nonneg_iff.mp h).1
    simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] at h'
    linarith
  · have h1 : (proj A * Ym * proj A).trace.re ≤ c' * A.card := htr_up Ym c' hupm
    have hplus : (((c' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + Ym).PosSemidef :=
      (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hc'.le)).add hYm
    have h2 : (proj A * (Ym * Ym) * proj A).trace.re ≤ c' ^ 2 * A.card :=
      htr_up (Ym * Ym) (c' ^ 2) (loewner_sq_le Ym c' hc' hupm hplus)
    have h1P : (1 - proj A).PosSemidef := by
      have e : (1 : Matrix (Fin n) (Fin n) ℂ) - proj A =
          Matrix.diagonal (fun i => ((if i ∈ A then 0 else 1 : ℝ) : ℂ)) := by
        rw [proj, ← Matrix.diagonal_one, Matrix.diagonal_sub]
        congr 1
        funext i
        split_ifs <;> simp
      rw [e, Matrix.posSemidef_diagonal_iff]
      intro i
      refine Complex.zero_le_real.mpr ?_
      split_ifs <;> norm_num
    have h3 : (proj A * (Ym * Ym) * proj A -
        proj A * Ym * proj A * (proj A * Ym * proj A)).PosSemidef := by
      have h := h1P.mul_mul_conjTranspose_same (proj A * Ym)
      have e : proj A * (Ym * Ym) * proj A - proj A * Ym * proj A * (proj A * Ym * proj A) =
          proj A * Ym * (1 - proj A) * (proj A * Ym)ᴴ := by
        rw [Matrix.conjTranspose_mul, proj_conj, hYm.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one]
        have e2 : proj A * Ym * proj A * (proj A * Ym * proj A) =
            proj A * Ym * (proj A * proj A) * (Ym * proj A) := by
          simp only [Matrix.mul_assoc]
        rw [e2, proj_mul]
        simp only [Matrix.mul_assoc]
      rw [e]
      exact h
    have h4 := (Complex.nonneg_iff.mp h3.trace_nonneg).1
    rw [Matrix.trace_sub, Complex.sub_re] at h4
    rw [Matrix.trace_add, Complex.add_re]
    nlinarith

/-- If `g ⪯ A` and `θ A ⪯ B` (`0 < θ ≤ 1`) then `B⁻¹ - A⁻¹ ⪯ (θ⁻¹ - 1) g⁻¹`. -/
private lemma inv_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (g θ : ℝ) (hg : 0 < g) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hAg : (A - ((g : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hBA : (B - ((θ : ℝ) : ℂ) • A).PosSemidef) :
    ((((θ⁻¹ - 1) * g⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (B⁻¹ - A⁻¹)).PosSemidef := by
  have h2 : (((θ⁻¹ : ℝ) : ℂ) • A⁻¹ - B⁻¹).PosSemidef := by
    refine inv_anti A B hA hB θ⁻¹ (inv_pos.mpr hθ) ?_
    have e : ((θ⁻¹ : ℝ) : ℂ) • B - A = ((θ⁻¹ : ℝ) : ℂ) • (B - ((θ : ℝ) : ℂ) • A) := by
      rw [smul_sub, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hθ.ne', Complex.ofReal_one,
        one_smul]
    rw [e]
    exact hBA.smul (Complex.zero_le_real.mpr (inv_pos.mpr hθ).le)
  have h3 : (((g⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A⁻¹).PosSemidef := by
    have h := inv_anti 1 A Matrix.PosDef.one hA g⁻¹ (inv_pos.mpr hg) (by
      have e : ((g⁻¹ : ℝ) : ℂ) • A - 1 =
          ((g⁻¹ : ℝ) : ℂ) • (A - ((g : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [smul_sub, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hg.ne', Complex.ofReal_one,
          one_smul]
      rw [e]
      exact hAg.smul (Complex.zero_le_real.mpr (inv_pos.mpr hg).le))
    rwa [inv_one] at h
  have hθi : 0 ≤ θ⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ hθ).mpr hθ1)
  have e : (((θ⁻¹ - 1) * g⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (B⁻¹ - A⁻¹) =
      (((θ⁻¹ : ℝ) : ℂ) • A⁻¹ - B⁻¹) +
        ((θ⁻¹ - 1 : ℝ) : ℂ) • (((g⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A⁻¹) := by
    push_cast
    module
  rw [e]
  exact h2.add (h3.smul (Complex.zero_le_real.mpr hθi))

/-- A Hermitian matrix of operator norm at most `c` lies between `-c` and `c` in the Loewner order. -/
private lemma opnorm_form {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) (c : ℝ)
    (h : WHMultiplicativity.schattenNorm ⊤ X ≤ c) :
    (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
      (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef := by
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ c := by
    simpa [WHMultiplicativity.schattenNorm] using h
  have key : ∀ v : Fin n → ℂ, |(star v ⬝ᵥ (X *ᵥ v)).re| ≤ c * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    set w : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v with hw
    have h1 : inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w) = star v ⬝ᵥ (X *ᵥ v) := by
      rw [hw, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    have h2 : ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖ ≤ c * ‖w‖ ^ 2 := by
      calc ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖
          ≤ ‖w‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X w‖ := norm_inner_le_norm _ _
        _ ≤ ‖w‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖w‖ * (c * ‖w‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
        _ = c * ‖w‖ ^ 2 := by ring
    have h3 : ‖w‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [h1, h3] at h2
    exact (Complex.abs_re_le_norm _).trans h2
  have hsq : ∀ v : Fin n → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have him : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).im = 0 := fun v =>
    hX.im_star_dotProduct_mulVec_self v
  have hc1 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.sub hX) fun v => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.2]
    · rw [Complex.sub_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, sub_zero]
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.add hX) fun v => ?_
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.1]
    · rw [Complex.add_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, add_zero]


/-- Loewner bounds for one member `R = r(1 + ξX)` of the family and its occupation matrix. -/
private lemma fam_facts {n : ℕ} (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    (fugacityFamily ν ξ X).PosSemidef ∧ (1 - fugacityFamily ν ξ X).PosDef ∧
    fugacityFamily ν ξ X * (1 - fugacityFamily ν ξ X)⁻¹ = (1 - fugacityFamily ν ξ X)⁻¹ - 1 ∧
    (fugacityFamily ν ξ X * (1 - fugacityFamily ν ξ X)⁻¹ -
      ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
    (((9 / 5 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      fugacityFamily ν ξ X * (1 - fugacityFamily ν ξ X)⁻¹).PosSemidef ∧
    ((1 - fugacityFamily ν ξ X) -
      ((5 / 14 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have hXh : (X : Matrix (Fin n) (Fin n) ℂ).IsHermitian := X.2.1
  have hop : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ 4 := hX
  obtain ⟨hminus, hplus⟩ := opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) hXh 4 hop
  have h14 : 0 < 1 - 4 * ξ := by linarith
  have h1ν : (0 : ℝ) < 1 + ν := by linarith
  set r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν)) with hr
  have hrpos : 0 < r := by positivity
  set u : ℝ := ν / (1 + ν) with hu
  have hu0 : 0 < u := by positivity
  have huν : u * (1 + ν) = ν := by
    rw [hu]
    field_simp
  have hu2 : u ≤ 1 / 2 := by
    rw [hu, div_le_iff₀ h1ν]
    linarith
  have hrt : r * (1 - 4 * ξ) = u := by
    rw [hr, hu]
    field_simp
  have hq : r * (1 + 4 * ξ) ≤ 9 / 7 * u := by
    rw [← hrt]
    have h := mul_le_mul_of_nonneg_left (show 1 + 4 * ξ ≤ 9 / 7 * (1 - 4 * ξ) by linarith) hrpos.le
    linarith
  set g : ℝ := 1 - r * (1 + 4 * ξ) with hg
  have hg514 : 5 / 14 ≤ g := by
    rw [hg]
    linarith
  have hgpos : 0 < g := by linarith
  have hginv : g⁻¹ ≤ 9 / 5 * ν + 1 := by
    rw [inv_le_iff_one_le_mul₀ hgpos]
    have h1 : 1 - 9 / 7 * u ≤ g := by
      rw [hg]
      linarith
    have h2 : (0 : ℝ) ≤ 9 / 5 * ν + 1 := by positivity
    have h3 : 1 ≤ (9 / 5 * ν + 1) * (1 - 9 / 7 * u) := by
      nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr hν1)]
    have h4 : (9 / 5 * ν + 1) * (1 - 9 / 7 * u) ≤ (9 / 5 * ν + 1) * g :=
      mul_le_mul_of_nonneg_left h1 h2
    linarith [mul_comm g (9 / 5 * ν + 1)]
  have hRdef : fugacityFamily ν ξ X =
      ((r : ℝ) : ℂ) • (1 + ((ξ : ℝ) : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) := rfl
  set R : Matrix (Fin n) (Fin n) ℂ := fugacityFamily ν ξ X with hRset
  have e1 : R - ((u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef, ← hrt]
    push_cast
    module
  have hRν : (R - ((u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [e1]
    exact hplus.smul (Complex.zero_le_real.mpr (by positivity))
  have hRpsd : R.PosSemidef := by
    have e : R = (R - ((u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [sub_add_cancel]
    rw [e]
    exact hRν.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hu0.le))
  have e2 : 1 - R = ((g : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
      ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef, hg]
    push_cast
    module
  have hrest : (((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      (X : Matrix (Fin n) (Fin n) ℂ))).PosSemidef :=
    hminus.smul (Complex.zero_le_real.mpr (by positivity))
  have hR1 : (1 - R).PosDef := by
    rw [e2]
    exact (Matrix.PosDef.one.smul (by exact_mod_cast hgpos)).add_posSemidef hrest
  have hunit : IsUnit (1 - R).det := (Matrix.isUnit_iff_isUnit_det _).mp hR1.isUnit
  have hN : R * (1 - R)⁻¹ = (1 - R)⁻¹ - 1 := by
    have h1 : R * (1 - R)⁻¹ = (1 - (1 - R)) * (1 - R)⁻¹ := by rw [sub_sub_cancel]
    rw [h1, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_nonsing_inv _ hunit]
  -- `(1 - R) ⪰ g`
  have hlow : ((1 - R) - ((g : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [e2, add_sub_cancel_left]
    exact hrest
  -- `T ⪯ g⁻¹`
  have hTup : (((g⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R)⁻¹).PosSemidef := by
    have h := inv_anti 1 (1 - R) Matrix.PosDef.one hR1 g⁻¹ (inv_pos.mpr hgpos) (by
      have e : ((g⁻¹ : ℝ) : ℂ) • (1 - R) - 1 =
          ((g⁻¹ : ℝ) : ℂ) • ((1 - R) - ((g : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [smul_sub _ (1 - R), smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hgpos.ne',
          Complex.ofReal_one, one_smul]
      rw [e]
      exact hlow.smul (Complex.zero_le_real.mpr (inv_pos.mpr hgpos).le))
    rwa [inv_one] at h
  -- `T ⪰ 1 + ν`
  have hTlo : ((1 - R)⁻¹ - ((1 + ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    have hu1 : (1 + ν)⁻¹ = 1 - u := by
      rw [hu]
      field_simp
      ring
    have h := inv_anti (1 - R) 1 hR1 Matrix.PosDef.one (1 + ν)⁻¹ (inv_pos.mpr h1ν) (by
      have e : (((1 + ν)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R) =
          R - ((u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        rw [hu1]
        push_cast
        module
      rw [e]
      exact hRν)
    rw [inv_one] at h
    have e : (1 - R)⁻¹ - ((1 + ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((1 + ν : ℝ) : ℂ) • ((((1 + ν)⁻¹ : ℝ) : ℂ) • (1 - R)⁻¹ - 1) := by
      rw [smul_sub, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h1ν.ne', Complex.ofReal_one,
        one_smul]
    rw [e]
    exact h.smul (Complex.zero_le_real.mpr h1ν.le)
  refine ⟨hRpsd, hR1, hN, ?_, ?_, ?_⟩
  · rw [hN]
    have e : (1 - R)⁻¹ - 1 - ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
        (1 - R)⁻¹ - ((1 + ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      push_cast
      module
    rw [e]
    exact hTlo
  · rw [hN]
    have e : ((9 / 5 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - ((1 - R)⁻¹ - 1) =
        (((g⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R)⁻¹) +
          ((9 / 5 * ν + 1 - g⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      push_cast
      module
    rw [e]
    exact hTup.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith)))
  · have e : (1 - R) - ((5 / 14 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((1 - R) - ((g : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
          ((g - 5 / 14 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      push_cast
      module
    rw [e]
    exact hlow.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith)))

/-- Two members of the family differ by at most `8 r ξ` in the Loewner order. -/
private lemma fam_pair {n : ℕ} (ν ξ : ℝ) (hν0 : 0 < ν) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 32)
    (X₁ : Herm0 n) (hX₁ : X₁ ∈ Gsupp n) (X₂ : Herm0 n) (hX₂ : X₂ ∈ Gsupp n) :
    (fugacityFamily ν ξ X₁ - fugacityFamily ν ξ X₂ +
      ((8 * (ν / ((1 - 4 * ξ) * (1 + ν)) * ξ) : ℝ) : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  obtain ⟨_, hplus⟩ := opnorm_form (X₁ : Matrix (Fin n) (Fin n) ℂ) X₁.2.1 4 hX₁
  obtain ⟨hminus, _⟩ := opnorm_form (X₂ : Matrix (Fin n) (Fin n) ℂ) X₂.2.1 4 hX₂
  have h14 : 0 < 1 - 4 * ξ := by linarith
  set r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν)) with hr
  have hrpos : 0 < r := by positivity
  have hR1 : fugacityFamily ν ξ X₁ =
      ((r : ℝ) : ℂ) • (1 + ((ξ : ℝ) : ℂ) • (X₁ : Matrix (Fin n) (Fin n) ℂ)) := rfl
  have hR2 : fugacityFamily ν ξ X₂ =
      ((r : ℝ) : ℂ) • (1 + ((ξ : ℝ) : ℂ) • (X₂ : Matrix (Fin n) (Fin n) ℂ)) := rfl
  have e : fugacityFamily ν ξ X₁ - fugacityFamily ν ξ X₂ +
      ((8 * (r * ξ) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ((r * ξ : ℝ) : ℂ) • ((((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X₁ : Matrix (Fin n) (Fin n) ℂ)) + (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        (X₂ : Matrix (Fin n) (Fin n) ℂ))) := by
    rw [hR1, hR2]
    push_cast
    module
  rw [e]
  exact (hplus.add hminus).smul (Complex.zero_le_real.mpr (by positivity))

/-- `0 ⪯ R ⪯ 1 ⇒ (1 - R)² ⪯ 1`. -/
private lemma one_sub_sq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosSemidef) : (1 - (1 - R) * (1 - R)).PosSemidef := by
  have h1 : (((1 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R)).PosSemidef := by
    have e : ((1 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R) = R := by
      rw [Complex.ofReal_one, one_smul]
      abel
    rw [e]
    exact hR
  have h2 : (((1 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (1 - R)).PosSemidef :=
    (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr zero_le_one)).add hR1
  have h := loewner_sq_le (1 - R) 1 one_pos h1 h2
  simpa using h

/-- Unitary conjugation of `1 - Z`. -/
private lemma conj_one_sub {n : ℕ} (U Z : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1) :
    U * (1 - Z) * Uᴴ = 1 - U * Z * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]

/-- Assembly of the conclusions once the order `(R₊, R₋)` and the set `A` are chosen. -/
private lemma wrap {n : ℕ} (Rp Rm U : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ)
    (A : Finset (Fin n)) (ν ξ a : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hU1 : Uᴴ * U = 1)
    (hdiff : U * (Rp * (1 - Rp)⁻¹ - Rm * (1 - Rm)⁻¹) * Uᴴ =
      Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)))
    (hlow : (Rm * (1 - Rm)⁻¹ - ((ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hupm : (((9 / 5 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      Rm * (1 - Rm)⁻¹).PosSemidef)
    (hupp : (((9 / 5 * ν : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      Rp * (1 - Rp)⁻¹).PosSemidef)
    (hA : ∀ i ∈ A, 0 ≤ e i) (hκ : ∀ i ∈ A, e i ≤ 120 * ν * ξ)
    (hL : 1 / 4 * a * n * ν * ξ ≤ ∑ i ∈ A, e i) :
    (proj A * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * proj A).PosSemidef ∧
    (proj A * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) * proj A - proj A * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * proj A).PosSemidef ∧
    (((120 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - proj A * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) * proj A).PosSemidef ∧
    1 / 4 * a * n * ν * ξ ≤ (proj A * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) * proj A - proj A * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * proj A).trace.re ∧
    (proj A * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) * proj A - proj A * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * proj A).trace.re ≤ 120 * A.card * ν * ξ ∧
    1 / 4 * A.card * ν ≤ (proj A * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * proj A).trace.re ∧
    (proj A * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * proj A + proj A * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * proj A * (proj A * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * proj A)).trace.re ≤ 120 * A.card * ν := by
  have hU2 : U * Uᴴ = 1 := mul_eq_one_comm.mp hU1
  have hconj1 : ∀ (N : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      U * (N - c • (1 : Matrix (Fin n) (Fin n) ℂ)) * Uᴴ = U * N * Uᴴ - c • 1 := by
    intro N c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
  have hconj2 : ∀ (N : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      U * (c • (1 : Matrix (Fin n) (Fin n) ℂ) - N) * Uᴴ = c • 1 - U * N * Uᴴ := by
    intro N c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := core (U * (Rp * (1 - Rp)⁻¹) * Uᴴ)
    (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) e A ν (9 / 5 * ν) hν0.le (by positivity)
    (by rw [← Matrix.sub_mul, ← Matrix.mul_sub]; exact hdiff) hA
    (by rw [← hconj1]; exact hlow.mul_mul_conjTranspose_same U)
    (by rw [← hconj2]; exact hupm.mul_mul_conjTranspose_same U)
    (by rw [← hconj2]; exact hupp.mul_mul_conjTranspose_same U)
  have hcard : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  refine ⟨c1, c2, c3 120 (by linarith), ?_, ?_, ?_, ?_⟩
  · rw [c4]
    exact hL
  · rw [c4]
    calc ∑ i ∈ A, e i ≤ ∑ _i ∈ A, 120 * ν * ξ := Finset.sum_le_sum hκ
      _ = 120 * A.card * ν * ξ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  · nlinarith [mul_nonneg hcard hν0.le]
  · refine c6.trans ?_
    have h : 9 / 5 * ν + (9 / 5 * ν) ^ 2 ≤ 120 * ν := by nlinarith
    calc (9 / 5 * ν + (9 / 5 * ν) ^ 2) * A.card ≤ 120 * ν * A.card :=
          mul_le_mul_of_nonneg_right h hcard
      _ = 120 * A.card * ν := by ring

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 32 →
      ∀ X₁ ∈ Gsupp n, ∀ X₂ ∈ Gsupp n, ∀ a : ℝ, 0 < a →
        a * n ≤ WHMultiplicativity.schattenNorm 1 ((X₂ - X₁ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) →
        ∃ Rp Rm : Matrix (Fin n) (Fin n) ℂ,
          ((Rp = fugacityFamily ν ξ X₁ ∧ Rm = fugacityFamily ν ξ X₂) ∨
            (Rp = fugacityFamily ν ξ X₂ ∧ Rm = fugacityFamily ν ξ X₁)) ∧
          ∃ (U : Matrix (Fin n) (Fin n) ℂ) (A : Finset (Fin n)), Uᴴ * U = 1 ∧
            (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
              Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).PosSemidef ∧
            (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) -
              Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).PosSemidef ∧
            (((C : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
              Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).PosSemidef ∧
            c * a * n * ν * ξ ≤
              (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) *
                  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) -
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).trace.re ∧
            (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) *
                  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) -
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).trace.re ≤ C * A.card * ν * ξ ∧
            c * A.card * ν ≤
              (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).trace.re ∧
            ((Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)) +
              (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)) *
              (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0))).trace.re ≤ C * A.card * ν := by
  refine ⟨1 / 4, by norm_num, 120, by norm_num, ?_⟩
  intro n hn ν hνn hν1 ξ hξ0 hξ1 X₁ hX₁ X₂ hX₂ a ha hnorm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := lt_of_lt_of_le (by positivity) hνn
  obtain ⟨hR1psd, hR1pd, hN1, hN1lo, hN1up, hR1g⟩ := fam_facts ν ξ hν0 hν1 hξ0 hξ1 X₁ hX₁
  obtain ⟨hR2psd, hR2pd, hN2, hN2lo, hN2up, hR2g⟩ := fam_facts ν ξ hν0 hν1 hξ0 hξ1 X₂ hX₂
  have hp12 := fam_pair ν ξ hν0 hξ0 hξ1 X₁ hX₁ X₂ hX₂
  have hp21 := fam_pair ν ξ hν0 hξ0 hξ1 X₂ hX₂ X₁ hX₁
  have hR1def : fugacityFamily ν ξ X₁ = ((ν / ((1 - 4 * ξ) * (1 + ν)) : ℝ) : ℂ) •
      (1 + ((ξ : ℝ) : ℂ) • (X₁ : Matrix (Fin n) (Fin n) ℂ)) := rfl
  have hR2def : fugacityFamily ν ξ X₂ = ((ν / ((1 - 4 * ξ) * (1 + ν)) : ℝ) : ℂ) •
      (1 + ((ξ : ℝ) : ℂ) • (X₂ : Matrix (Fin n) (Fin n) ℂ)) := rfl
  set R₁ : Matrix (Fin n) (Fin n) ℂ := fugacityFamily ν ξ X₁ with hR₁
  set R₂ : Matrix (Fin n) (Fin n) ℂ := fugacityFamily ν ξ X₂ with hR₂
  -- scalars
  have h14 : 7 / 8 < 1 - 4 * ξ := by linarith
  have hD0 : 0 < (1 - 4 * ξ) * (1 + ν) := by
    have : 0 < 1 - 4 * ξ := by linarith
    positivity
  have hD1 : 7 / 8 * (1 + ν) ≤ (1 - 4 * ξ) * (1 + ν) :=
    mul_le_mul_of_nonneg_right h14.le (by linarith)
  have hD2 : (1 - 4 * ξ) * (1 + ν) ≤ 2 := by nlinarith
  set r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν)) with hr
  have hrpos : 0 < r := by positivity
  have hrlo : ν / 2 ≤ r := div_le_div_of_nonneg_left hν0.le hD0 hD2
  have hrup : r ≤ 8 / 7 * ν := by
    rw [hr, div_le_iff₀ hD0]
    nlinarith [mul_le_mul_of_nonneg_left hD1 hν0.le]
  have hr47 : r ≤ 4 / 7 := by
    rw [hr, div_le_iff₀ hD0]
    linarith
  have hrξ0 : 0 < r * ξ := by positivity
  have hrξ : r * ξ ≤ 1 / 56 := by nlinarith
  set θ : ℝ := 1 - 112 / 5 * (r * ξ) with hθ
  have hθ0 : 3 / 5 ≤ θ := by rw [hθ]; linarith
  have hθpos : 0 < θ := by linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hKle : (θ⁻¹ - 1) * (5 / 14 : ℝ)⁻¹ ≤ 120 * ν * ξ := by
    have h1 : θ⁻¹ ≤ 1 + 112 / 3 * (r * ξ) := by
      rw [inv_le_iff_one_le_mul₀ hθpos, hθ]
      nlinarith [mul_nonneg hrξ0.le (sub_nonneg.mpr hrξ)]
    have h2 : r * ξ ≤ 8 / 7 * ν * ξ := mul_le_mul_of_nonneg_right hrup hξ0.le
    have h3 : ((5 : ℝ) / 14)⁻¹ = 14 / 5 := by norm_num
    rw [h3]
    nlinarith
  -- `θ (1 - R₁) ⪯ 1 - R₂` and symmetrically
  have h21 : ((1 - R₂) - ((θ : ℝ) : ℂ) • (1 - R₁)).PosSemidef := by
    have e : (1 - R₂) - ((θ : ℝ) : ℂ) • (1 - R₁) =
        (R₁ - R₂ + ((8 * (r * ξ) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
          ((112 / 5 * (r * ξ) : ℝ) : ℂ) •
            ((1 - R₁) - ((5 / 14 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hθ]
      push_cast
      module
    rw [e]
    exact hp12.add (hR1g.smul (Complex.zero_le_real.mpr (by positivity)))
  have h12 : ((1 - R₁) - ((θ : ℝ) : ℂ) • (1 - R₂)).PosSemidef := by
    have e : (1 - R₁) - ((θ : ℝ) : ℂ) • (1 - R₂) =
        (R₂ - R₁ + ((8 * (r * ξ) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
          ((112 / 5 * (r * ξ) : ℝ) : ℂ) •
            ((1 - R₂) - ((5 / 14 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hθ]
      push_cast
      module
    rw [e]
    exact hp21.add (hR2g.smul (Complex.zero_le_real.mpr (by positivity)))
  have hK21 := inv_sub_le (1 - R₁) (1 - R₂) hR1pd hR2pd (5 / 14) θ (by norm_num) hθpos hθ1
    hR1g h21
  have hK12 := inv_sub_le (1 - R₂) (1 - R₁) hR2pd hR1pd (5 / 14) θ (by norm_num) hθpos hθ1
    hR2g h12
  set K : ℝ := (θ⁻¹ - 1) * (5 / 14 : ℝ)⁻¹ with hK
  have hunit1 : IsUnit (1 - R₁).det := (Matrix.isUnit_iff_isUnit_det _).mp hR1pd.isUnit
  have hunit2 : IsUnit (1 - R₂).det := (Matrix.isUnit_iff_isUnit_det _).mp hR2pd.isUnit
  -- diagonalize `Δ = T₁ - T₂`
  have hΔh : ((1 - R₁)⁻¹ - (1 - R₂)⁻¹).IsHermitian :=
    hR1pd.isHermitian.inv.sub hR2pd.isHermitian.inv
  obtain ⟨U, e, hU1, hU2, hUe⟩ := diag_data _ hΔh
  have he_up : ∀ i, e i ≤ K := by
    intro i
    have h := (hK12.mul_mul_conjTranspose_same U).diag_nonneg (i := i)
    have e' : U * (((K : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - ((1 - R₁)⁻¹ - (1 - R₂)⁻¹)) * Uᴴ =
        ((K : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hUe, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
    rw [e', Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
      smul_eq_mul, mul_one, ← Complex.ofReal_sub] at h
    linarith [Complex.zero_le_real.mp h]
  have he_lo : ∀ i, -K ≤ e i := by
    intro i
    have h := (hK21.mul_mul_conjTranspose_same U).diag_nonneg (i := i)
    have e' : U * (((K : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - ((1 - R₂)⁻¹ - (1 - R₁)⁻¹)) * Uᴴ =
        ((K : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) := by
      have h0 : (1 - R₂)⁻¹ - (1 - R₁)⁻¹ = -((1 - R₁)⁻¹ - (1 - R₂)⁻¹) := (neg_sub _ _).symm
      rw [h0, sub_neg_eq_add, Matrix.mul_add, Matrix.add_mul, hUe, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hU2]
    rw [e', Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
      smul_eq_mul, mul_one, ← Complex.ofReal_add] at h
    linarith [Complex.zero_le_real.mp h]
  -- the trace-norm lower bound
  have hHh : ((X₂ : Matrix (Fin n) (Fin n) ℂ) - (X₁ : Matrix (Fin n) (Fin n) ℂ)).IsHermitian :=
    X₂.2.1.sub X₁.2.1
  obtain ⟨W, hW1, hWn⟩ := schatten_one_herm _ hHh
  have hnorm' : a * n ≤
      (((X₂ : Matrix (Fin n) (Fin n) ℂ) - (X₁ : Matrix (Fin n) (Fin n) ℂ)) * W).trace.re := by
    rw [← hWn]
    exact hnorm
  have hRd : R₂ - R₁ = ((r * ξ : ℝ) : ℂ) •
      ((X₂ : Matrix (Fin n) (Fin n) ℂ) - (X₁ : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hR1def, hR2def]
    push_cast
    module
  have hres : (1 - R₁) * ((1 - R₁)⁻¹ - (1 - R₂)⁻¹) * (1 - R₂) = -(R₂ - R₁) := by
    rw [Matrix.mul_sub (1 - R₁) ((1 - R₁)⁻¹) ((1 - R₂)⁻¹), Matrix.mul_nonsing_inv _ hunit1,
      Matrix.sub_mul 1 _ (1 - R₂), Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hunit2, Matrix.mul_one]
    abel
  have hΔ : (1 - R₁)⁻¹ - (1 - R₂)⁻¹ = Uᴴ * Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * U := by
    have h : Uᴴ * (U * ((1 - R₁)⁻¹ - (1 - R₂)⁻¹) * Uᴴ) * U =
        (Uᴴ * U) * ((1 - R₁)⁻¹ - (1 - R₂)⁻¹) * (Uᴴ * U) := by
      simp only [Matrix.mul_assoc]
    rw [← hUe, h, hU1, Matrix.one_mul, Matrix.mul_one]
  have hP : (1 - U * (1 - R₂) * (U * (1 - R₂))ᴴ).PosSemidef := by
    have e' : 1 - U * (1 - R₂) * (U * (1 - R₂))ᴴ = U * (1 - (1 - R₂) * (1 - R₂)) * Uᴴ := by
      rw [conj_one_sub U _ hU2, Matrix.conjTranspose_mul, hR2pd.isHermitian.eq]
      simp only [Matrix.mul_assoc]
    rw [e']
    exact (one_sub_sq R₂ hR2psd hR2pd.posSemidef).mul_mul_conjTranspose_same U
  have hQ : (1 - (W * (1 - R₁) * Uᴴ)ᴴ * (W * (1 - R₁) * Uᴴ)).PosSemidef := by
    have e' : 1 - (W * (1 - R₁) * Uᴴ)ᴴ * (W * (1 - R₁) * Uᴴ) =
        U * (1 - (1 - R₁) * (1 - R₁)) * Uᴴ := by
      have h : U * ((1 - R₁) * Wᴴ) * (W * (1 - R₁) * Uᴴ) =
          U * ((1 - R₁) * (Wᴴ * W) * (1 - R₁)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
      rw [conj_one_sub U _ hU2, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hR1pd.isHermitian.eq, h, hW1, Matrix.mul_one]
    rw [e']
    exact (one_sub_sq R₁ hR1psd hR1pd.posSemidef).mul_mul_conjTranspose_same U
  have hhol := holder (U * (1 - R₂)) (W * (1 - R₁) * Uᴴ) e hP hQ
  have hkey : (r * ξ) *
      (((X₂ : Matrix (Fin n) (Fin n) ℂ) - (X₁ : Matrix (Fin n) (Fin n) ℂ)) * W).trace.re =
      -(Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) *
        (U * (1 - R₂) * (W * (1 - R₁) * Uᴴ))).trace.re := by
    have h1 : ((r * ξ : ℝ) : ℂ) •
        (((X₂ : Matrix (Fin n) (Fin n) ℂ) - (X₁ : Matrix (Fin n) (Fin n) ℂ)) * W) =
        -((1 - R₁) * (Uᴴ * Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * U) * (1 - R₂) * W) := by
      rw [← Matrix.smul_mul, ← hRd, ← hΔ, hres, Matrix.neg_mul, neg_neg]
    have h2 : ((1 - R₁) * (Uᴴ * Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * U) * (1 - R₂) *
        W).trace = (Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) *
          (U * (1 - R₂) * (W * (1 - R₁) * Uᴴ))).trace := by
      have h3 : (1 - R₁) * (Uᴴ * Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * U) * (1 - R₂) * W =
          ((1 - R₁) * Uᴴ) * (Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (U * (1 - R₂)) * W) := by
        simp only [Matrix.mul_assoc]
      rw [h3, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.trace.re) h1
    simp only [Matrix.trace_smul, Matrix.trace_neg, Complex.neg_re, smul_eq_mul,
      Complex.re_ofReal_mul] at h4
    rw [h4, h2]
  have hsum : ν / 2 * ξ * (a * n) ≤ ∑ i, |e i| := by
    have han : 0 ≤ a * n := by positivity
    calc ν / 2 * ξ * (a * n) ≤ r * ξ * (a * n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrlo hξ0.le) han
      _ ≤ r * ξ * (((X₂ : Matrix (Fin n) (Fin n) ℂ) - (X₁ : Matrix (Fin n) (Fin n) ℂ)) *
            W).trace.re := mul_le_mul_of_nonneg_left hnorm' hrξ0.le
      _ = -(Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) *
            (U * (1 - R₂) * (W * (1 - R₁) * Uᴴ))).trace.re := hkey
      _ ≤ |(Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) *
            (U * (1 - R₂) * (W * (1 - R₁) * Uᴴ))).trace.re| := neg_le_abs _
      _ ≤ ∑ i, |e i| := hhol
  -- the sign choice
  have hsplit : ∑ i, |e i| = ∑ i ∈ Finset.univ.filter (fun i => 0 < e i), e i +
      ∑ i ∈ Finset.univ.filter (fun i => e i < 0), -e i := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases lt_trichotomy (e i) 0 with h | h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos h, abs_of_neg h, zero_add]
    · rw [h]
      simp
    · rw [if_pos h, if_neg (not_lt.mpr h.le), abs_of_pos h, add_zero]
  by_cases hcase : ∑ i ∈ Finset.univ.filter (fun i => e i < 0), -e i ≤
      ∑ i ∈ Finset.univ.filter (fun i => 0 < e i), e i
  · refine ⟨R₁, R₂, Or.inl ⟨rfl, rfl⟩, U, Finset.univ.filter (fun i => 0 < e i), hU1, ?_⟩
    exact wrap R₁ R₂ U e _ ν ξ a hν0 hν1 hU1
      (by rw [hN1, hN2, sub_sub_sub_cancel_right]; exact hUe) hN2lo hN2up hN1up
      (fun i hi => (Finset.mem_filter.mp hi).2.le) (fun i _ => (he_up i).trans hKle)
      (by linarith)
  · refine ⟨R₂, R₁, Or.inr ⟨rfl, rfl⟩, U, Finset.univ.filter (fun i => e i < 0), hU1, ?_⟩
    have hdiff : U * (R₂ * (1 - R₂)⁻¹ - R₁ * (1 - R₁)⁻¹) * Uᴴ =
        Matrix.diagonal (fun i => ((-e i : ℝ) : ℂ)) := by
      have h0 : (1 - R₂)⁻¹ - (1 - R₁)⁻¹ = -((1 - R₁)⁻¹ - (1 - R₂)⁻¹) := (neg_sub _ _).symm
      rw [hN1, hN2, sub_sub_sub_cancel_right, h0, Matrix.mul_neg, Matrix.neg_mul, hUe,
        Matrix.diagonal_neg]
      congr 1
      funext i
      push_cast
      rfl
    exact wrap R₂ R₁ U (fun i => -e i) _ ν ξ a hν0 hν1 hU1 hdiff hN1lo hN1up hN2up
      (fun i hi => by have := (Finset.mem_filter.mp hi).2; linarith)
      (fun i _ => by linarith [he_lo i])
      (by
        show 1 / 4 * a * n * ν * ξ ≤ ∑ i ∈ Finset.univ.filter (fun i => e i < 0), -e i
        linarith)
