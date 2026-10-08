-- Prove2me | solution 1 for BoydADMM.L1.covsel_X_update
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T07:40:48.68465+00:00
-- url     : https://prove2.me/submissions/be7c696a-4411-40b0-a015-75df2c700e02

import Definitions.Def_BoydADMM_L1_Basic
import Definitions.Def_BoydADMM_L1_CovSel
import Mathlib
set_option autoImplicit false
section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1
 theorem scalar_root (ρ μ : ℝ) (hρ : 0 < ρ) :
    0 < covselRoot ρ μ ∧ ρ * covselRoot ρ μ - 1 / covselRoot ρ μ = μ := by
  have hd : 0 ≤ μ ^ 2 + 4 * ρ := by positivity
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg (μ ^ 2 + 4 * ρ)
  have hp : 0 < μ + Real.sqrt (μ ^ 2 + 4 * ρ) := by
    nlinarith [sq_nonneg (μ + Real.sqrt (μ ^ 2 + 4 * ρ))]
  have ht : 0 < covselRoot ρ μ := div_pos hp (by positivity)
  refine ⟨ht, ?_⟩
  have he : ρ * (covselRoot ρ μ) ^ 2 - μ * covselRoot ρ μ - 1 = 0 := by
    unfold covselRoot
    field_simp
    simp only [mul_comm ρ 4] at *
    nlinarith
  apply (mul_right_cancel₀ (ne_of_gt ht))
  field_simp
  nlinarith [he]
end ADMMCodex

end

section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
open BoydADMM.L1
 theorem spectral_update {n : ℕ} (S Z U Q : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (μ : Fin n → ℝ) (hρ : 0 < ρ) (hQ₁ : Qᵀ * Q = 1) (hQ₂ : Q * Qᵀ = 1)
    (hdecomp : ρ • (Z - U) - S = Q * diagonal μ * Qᵀ) :
    (covselX ρ Q μ).PosDef ∧ ρ • covselX ρ Q μ - (covselX ρ Q μ)⁻¹ =
      ρ • (Z - U) - S := by
  let r : Fin n → ℝ := fun i => covselRoot ρ (μ i)
  have hr : ∀ i, 0 < r i := fun i => (scalar_root ρ (μ i) hρ).1
  have hj : Function.Injective (fun v : Fin n → ℝ => v ᵥ* Q) := by
    intro x y h
    have := congrArg (fun v => v ᵥ* Qᵀ) h
    simpa only [vecMul_vecMul, hQ₂, vecMul_one] using this
  have hp : (covselX ρ Q μ).PosDef := by
    have hd := (posDef_diagonal_iff.mpr hr).mul_mul_conjTranspose_same hj
    simpa [covselX, r] using hd
  have hi : (covselX ρ Q μ)⁻¹ = Q * diagonal (fun i => (r i)⁻¹) * Qᵀ := by
    apply inv_eq_right_inv
    change (Q * diagonal r * Qᵀ) * (Q * diagonal (fun i => (r i)⁻¹) * Qᵀ) = 1
    calc
      _ = Q * (diagonal r * (Qᵀ * Q) * diagonal (fun i => (r i)⁻¹)) * Qᵀ := by simp only [Matrix.mul_assoc]
      _ = Q * diagonal (fun _ => (1 : ℝ)) * Qᵀ := by
        rw [hQ₁, Matrix.mul_one, diagonal_mul_diagonal]
        have hd : (fun i => r i * (r i)⁻¹) = (fun _ => (1 : ℝ)) := by
          funext i
          exact mul_inv_cancel₀ (ne_of_gt (hr i))
        rw [hd]
      _ = 1 := by simpa only [diagonal_one, Matrix.mul_one] using hQ₂
  refine ⟨hp, ?_⟩
  rw [hi, hdecomp]
  change ρ • (Q * diagonal r * Qᵀ) - Q * diagonal (fun i => (r i)⁻¹) * Qᵀ = _
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 1
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simpa [r, one_div] using (scalar_root ρ (μ i) hρ).2
  · simp [diagonal_apply, h]
end ADMMCodex

end

section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
 theorem logdet_le_trace_sub_card {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) : Real.log A.det ≤ A.trace - n := by
  have hp : ∀ i, 0 < hA.1.eigenvalues i := hA.eigenvalues_pos
  rw [hA.1.det_eq_prod_eigenvalues, hA.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hp i))]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Real.log_le_sub_one_of_pos (hp i))
  simpa [Finset.sum_sub_distrib] using hb
end ADMMCodex

end

section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
 theorem logdet_tangent_of_factor {n : ℕ} (X Y A : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) (hA : A.PosDef) (hfac : A * A = X⁻¹) :
    Real.log Y.det - Real.log X.det ≤ (X⁻¹ * Y).trace - n := by
  have hinj : Function.Injective A.mulVec := mulVec_injective_iff_isUnit.mpr hA.isUnit
  have hT := hY.conjTranspose_mul_mul_same hinj
  have ht : (A * Y * A).PosDef := by
    simpa only [hA.1.eq] using hT
  have hb := logdet_le_trace_sub_card (A * Y * A) ht
  have htrace : (A * Y * A).trace = (X⁻¹ * Y).trace := by
    rw [trace_mul_cycle, hfac]
  have hdetX : X⁻¹.det = (X.det)⁻¹ := by simp
  have hlogfac : 2 * Real.log A.det = -Real.log X.det := by
    have he := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => Real.log B.det) hfac
    rw [det_mul, Real.log_mul (ne_of_gt hA.det_pos) (ne_of_gt hA.det_pos),
      hdetX, Real.log_inv] at he
    linarith
  rw [htrace, det_mul, det_mul,
    Real.log_mul (mul_ne_zero (ne_of_gt hA.det_pos) (ne_of_gt hY.det_pos)) (ne_of_gt hA.det_pos),
    Real.log_mul (ne_of_gt hA.det_pos) (ne_of_gt hY.det_pos)] at hb
  linarith
end ADMMCodex

end

section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
section
open scoped MatrixOrder
 theorem logdet_tangent {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    Real.log Y.det - Real.log X.det ≤ (X⁻¹ * Y).trace - n := by
  let A := CFC.sqrt X⁻¹
  have hn : 0 ≤ X⁻¹ := hX.inv.posSemidef.nonneg
  have hs : A * A = X⁻¹ := CFC.sqrt_mul_sqrt_self X⁻¹ hn
  have hA : A.PosDef := (CFC.sqrt_nonneg X⁻¹).posSemidef.posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff X⁻¹ hn).mpr hX.inv.isUnit)
  exact logdet_tangent_of_factor X Y A hX hY hA hs
end
end ADMMCodex

end

section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
open BoydADMM.L1
 theorem frobSq_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    frobSq (A + B) = frobSq A + 2 * (A * B).trace + frobSq B := by
  have he : frobSq (A+B) = ∑ i, ∑ j, ((A i j)^2 + 2 * A i j * B i j + (B i j)^2) := by
    unfold frobSq
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.add_apply]
    ring
  have ht : (A*B).trace = ∑ i, ∑ j, A i j * B i j := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    change (∑ j, A i j * B j i) = ∑ j, A i j * B i j
    apply Finset.sum_congr rfl
    intro j _
    rw [hB.apply i j]
  rw [he, ht]
  unfold frobSq
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
 theorem objective_gap {n : ℕ} (S Z U X Y : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) (hstat : S-X⁻¹+ρ • (X-Z+U)=0) :
    covselXObjective S Z U ρ Y - covselXObjective S Z U ρ X =
      (X⁻¹ * (Y-X)).trace - (Real.log Y.det-Real.log X.det) +
        (ρ/2)*frobSq (Y-X) := by
  have hd : (Y-X).IsSymm := (isHermitian_iff_isSymm.mp hY.1).sub
    (isHermitian_iff_isSymm.mp hX.1)
  have hy : Y-Z+U = (X-Z+U)+(Y-X) := by abel
  have hs : S = X⁻¹ - ρ • (X-Z+U) := by
    calc
      S = (S-X⁻¹+ρ • (X-Z+U)) + (X⁻¹-ρ • (X-Z+U)) := by abel
      _ = X⁻¹ - ρ • (X-Z+U) := by rw [hstat, zero_add]
  have ht : (S*Y).trace-(S*X).trace = (S*(Y-X)).trace := by
    rw [Matrix.mul_sub, trace_sub]
  unfold covselXObjective
  rw [hy, frobSq_add _ _ hd]
  have hts : (S*(Y-X)).trace = (X⁻¹*(Y-X)).trace - ρ*((X-Z+U)*(Y-X)).trace := by
    rw [hs, Matrix.sub_mul, trace_sub, Matrix.smul_mul, trace_smul]
    rfl
  linarith [ht, hts]
 theorem objective_gap_lower {n : ℕ} (S Z U X Y : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) (hstat : S-X⁻¹+ρ • (X-Z+U)=0) :
    (ρ/2)*frobSq (Y-X) ≤ covselXObjective S Z U ρ Y - covselXObjective S Z U ρ X := by
  rw [objective_gap S Z U X Y ρ hX hY hstat]
  have hi : X⁻¹*X=1 := X.nonsing_inv_mul ((isUnit_iff_isUnit_det X).mp hX.isUnit)
  have ht : (X⁻¹*(Y-X)).trace = (X⁻¹*Y).trace-n := by
    rw [Matrix.mul_sub, trace_sub, hi]
    simp
  rw [ht]
  linarith [logdet_tangent X Y hX hY]
end ADMMCodex

end

section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
open BoydADMM.L1
 theorem frobSq_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobSq A := by
  unfold frobSq
  positivity
 theorem frobSq_eq_zero_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : frobSq A = 0 ↔ A=0 := by
  constructor
  · intro h
    ext i j
    have hrow : (A i j)^2 ≤ ∑ k, (A i k)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)
    have hall : (∑ k, (A i k)^2) ≤ frobSq A :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (A k l))) (Finset.mem_univ i)
    simp only [Matrix.zero_apply]
    nlinarith
  · intro h
    simp [h, frobSq]
 theorem stationary_unique_optimizer {n : ℕ} (S Z U X : Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ) (hρ : 0<ρ) (hX : X.PosDef) (hstat : S-X⁻¹+ρ • (X-Z+U)=0) :
    IsUniqueMinimizerOn (covselXObjective S Z U ρ) {Y | Y.PosDef} X := by
  refine ⟨hX, ?_, ?_⟩
  · intro Y hY
    have hg := objective_gap_lower S Z U X Y ρ hX hY hstat
    have hn := mul_nonneg (le_of_lt (half_pos hρ)) (frobSq_nonneg (Y-X))
    linarith
  · intro Y hY hm
    have hg := objective_gap_lower S Z U X Y ρ hX hY hstat
    have hn := frobSq_nonneg (Y-X)
    have he : frobSq (Y-X)=0 := by nlinarith
    exact sub_eq_zero.mp ((frobSq_eq_zero_iff (Y-X)).mp he)
end ADMMCodex

end

set_option autoImplicit false
open Matrix BoydADMM.L1
 theorem solution {n : ℕ} (S Z U Q : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (μ : Fin n → ℝ)
    (hρ : 0 < ρ) (hS : S.IsSymm) (hZU : (Z - U).IsSymm)
    (hQ₁ : Qᵀ * Q = 1) (hQ₂ : Q * Qᵀ = 1)
    (hdecomp : ρ • (Z - U) - S = Q * Matrix.diagonal μ * Qᵀ) :
    IsUniqueMinimizerOn (covselXObjective S Z U ρ) {X | X.PosDef} (covselX ρ Q μ) := by
  obtain ⟨hp, he⟩ := ADMMCodex.spectral_update S Z U Q ρ μ hρ hQ₁ hQ₂ hdecomp
  apply ADMMCodex.stationary_unique_optimizer S Z U (covselX ρ Q μ) ρ hρ hp
  ext i j
  have hx := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) he
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.zero_apply] at hx ⊢
  linarith

#print axioms solution
