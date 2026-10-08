-- Prove2me | solution 1 for BoydADMM.L1.covsel_Z_update
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T08:01:45.514561+00:00
-- url     : https://prove2.me/submissions/fd3154fa-55c1-4b82-831a-cca5c5cf2710

import Definitions.Def_BoydADMM_L1_Basic
import Definitions.Def_BoydADMM_L1_CovSel
import Mathlib
set_option autoImplicit false
section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.Prox
 theorem soft_subgradient (lam ρ a z : ℝ) (hlam : 0≤lam) (hρ : 0<ρ) :
    lam * |softThreshold (lam/ρ) a| +
      ρ * (a-softThreshold (lam/ρ) a) * (z-softThreshold (lam/ρ) a) ≤ lam * |z| := by
  have hk : 0≤lam/ρ := div_nonneg hlam (le_of_lt hρ)
  have hmul : ρ * (lam/ρ)=lam := by field_simp
  by_cases hp : lam/ρ < a
  · simp only [softThreshold, if_pos hp]
    have ht : 0<a-lam/ρ := sub_pos.mpr hp
    have he : ρ*(a-(a-lam/ρ))=lam := by nlinarith [hmul]
    rw [abs_of_pos ht, he]
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self z) hlam]
  · by_cases hn : a < -(lam/ρ)
    · simp only [softThreshold, if_neg hp, if_pos hn]
      have ht : a+lam/ρ < 0 := by linarith
      have he : ρ*(a-(a+lam/ρ))= -lam := by nlinarith [hmul]
      rw [abs_of_neg ht, he]
      nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs z) hlam]
    · simp only [softThreshold, if_neg hp, if_neg hn, abs_zero, mul_zero, sub_zero, zero_add]
      have hu : ρ*a ≤ lam := by
        have := mul_le_mul_of_nonneg_left (le_of_not_gt hp) (le_of_lt hρ)
        nlinarith [hmul]
      have hl : -lam ≤ ρ*a := by
        have := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (le_of_lt hρ)
        nlinarith [hmul]
      by_cases hz : 0≤z
      · rw [abs_of_nonneg hz]
        exact mul_le_mul_of_nonneg_right hu hz
      · rw [abs_of_neg (lt_of_not_ge hz)]
        nlinarith [mul_le_mul_of_nonpos_right hl (le_of_lt (lt_of_not_ge hz))]
 theorem soft_gap (lam ρ a z : ℝ) (hlam : 0≤lam) (hρ : 0<ρ) :
    (ρ/2)*(z-softThreshold (lam/ρ) a)^2 ≤
      (lam*|z|+(ρ/2)*(a-z)^2) -
        (lam*|softThreshold (lam/ρ) a|+(ρ/2)*(a-softThreshold (lam/ρ) a)^2) := by
  have h := soft_subgradient lam ρ a z hlam hρ
  nlinarith
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

section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
open BoydADMM.L1 BoydADMM.Prox
 theorem z_objective_sum {n : ℕ} (lam ρ : ℝ) (X U Z : Matrix (Fin n) (Fin n) ℝ) :
    covselZObjective lam ρ X U Z = ∑ i, ∑ j,
      (lam*|Z i j|+(ρ/2)*((X i j+U i j)-Z i j)^2) := by
  unfold covselZObjective entrywiseL1 frobSq
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Matrix.sub_apply, Matrix.add_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
 theorem matrix_threshold {n : ℕ} (lam ρ : ℝ) (hlam : 0≤lam) (hρ : 0<ρ)
    (X U : Matrix (Fin n) (Fin n) ℝ) :
    IsUniqueMinimizerOn (covselZObjective lam ρ X U) Set.univ
      (Matrix.of fun i j => softThreshold (lam/ρ) (X i j+U i j)) := by
  let T : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => softThreshold (lam/ρ) (X i j+U i j)
  have gap (Y : Matrix (Fin n) (Fin n) ℝ) : (ρ/2)*frobSq (Y-T) ≤
      covselZObjective lam ρ X U Y - covselZObjective lam ρ X U T := by
    have hg : (∑ i, ∑ j, (ρ/2)*(Y i j-T i j)^2) ≤ ∑ i, ∑ j,
        ((lam*|Y i j|+(ρ/2)*((X i j+U i j)-Y i j)^2) -
          (lam*|T i j|+(ρ/2)*((X i j+U i j)-T i j)^2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact soft_gap lam ρ (X i j+U i j) (Y i j) hlam hρ
    rw [z_objective_sum, z_objective_sum]
    simpa only [frobSq, Matrix.sub_apply, Finset.sum_sub_distrib, ← Finset.mul_sum] using hg
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · intro Y _
    have hg := gap Y
    have hn := mul_nonneg (le_of_lt (half_pos hρ)) (frobSq_nonneg (Y-T))
    linarith
  · intro Y _ hm
    have hg := gap Y
    have hn := frobSq_nonneg (Y-T)
    have he : frobSq (Y-T)=0 := by nlinarith
    exact sub_eq_zero.mp ((frobSq_eq_zero_iff (Y-T)).mp he)
end ADMMCodex

end

set_option autoImplicit false
open Matrix BoydADMM.L1
theorem solution {n : ℕ} (lam ρ : ℝ) (hlam : 0 ≤ lam) (hρ : 0 < ρ)
    (X U : Matrix (Fin n) (Fin n) ℝ) :
    IsUniqueMinimizerOn (covselZObjective lam ρ X U) Set.univ
      (Matrix.of fun i j => BoydADMM.Prox.softThreshold (lam / ρ) (X i j + U i j)) := by
  exact ADMMCodex.matrix_threshold lam ρ hlam hρ X U



#print axioms solution
