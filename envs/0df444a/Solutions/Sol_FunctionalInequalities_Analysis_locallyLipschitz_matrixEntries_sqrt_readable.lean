-- Prove2me | solution 1 for FunctionalInequalities.Analysis.locallyLipschitz_matrixEntries_sqrt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:06.229182+00:00
-- url     : https://prove2.me/submissions/a44b949a-c08d-4ab2-9275-ad349f173fb5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Theorems.Thm_FunctionalInequalities_Analysis_exists_quadraticFloor_of_posDef_readable
import Theorems.Thm_FunctionalInequalities_Analysis_root_difference_bound_readable

section
noncomputable section
open scoped MatrixOrder Kronecker
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
section Frobenius
open Matrix Finset
open scoped RealInnerProductSpace
theorem FunctionalInequalities.Analysis.matrixEntries_norm_sq (A : Matrix ι ι ℝ) :
    ‖matrixEntries A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Fintype.sum_prod_type _
theorem FunctionalInequalities.Analysis.matrixEntries_inner (A B : Matrix ι ι ℝ) :
    ⟪matrixEntries A, matrixEntries B⟫ = ∑ i, ∑ j, A i j * B i j := by
  rw [PiLp.inner_apply]
  simp only [matrixEntries, PiLp.toLp_apply, Real.inner_apply]
  exact Fintype.sum_prod_type _
omit [Fintype ι] in
theorem FunctionalInequalities.Analysis.matrixEntries_sub (A B : Matrix ι ι ℝ) :
    matrixEntries (A - B) = matrixEntries A - matrixEntries B := by
  ext ij
  rfl
omit [Fintype ι] in
theorem FunctionalInequalities.Analysis.continuous_matrixEntries :
    Continuous (matrixEntries : Matrix ι ι ℝ → EuclideanSpace ℝ (ι × ι)) :=
  (PiLp.continuous_toLp 2 (fun _ : ι × ι => ℝ)).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
end Frobenius
section Floor
open Matrix Finset
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
variable [DecidableEq ι]
omit [DecidableEq ι] in
private theorem FunctionalInequalities.Analysis.outer_norm (v : ι → ℝ) : ‖matrixEntries (FunctionalInequalities.Analysis.outer v)‖ = ∑ i, (v i) ^ 2 := by
  have he : ‖matrixEntries (FunctionalInequalities.Analysis.outer v)‖ ^ 2 = (∑ i, (v i) ^ 2) ^ 2 := by
    rw [matrixEntries_norm_sq]
    simp only [FunctionalInequalities.Analysis.outer, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hp : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _hi => sq_nonneg _
  nlinarith [norm_nonneg (matrixEntries (FunctionalInequalities.Analysis.outer v))]
omit [DecidableEq ι] in
private theorem FunctionalInequalities.Analysis.outer_inner (D : Matrix ι ι ℝ) (v : ι → ℝ) :
    ⟪matrixEntries D, matrixEntries (FunctionalInequalities.Analysis.outer v)⟫ = v ⬝ᵥ (D *ᵥ v) := by
  rw [matrixEntries_inner]
  simp only [FunctionalInequalities.Analysis.outer, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring
omit [DecidableEq ι] in
/-- The quadratic form is controlled by the Frobenius norm. -/
theorem FunctionalInequalities.Analysis.abs_dotProduct_mulVec_le (D : Matrix ι ι ℝ) (v : ι → ℝ) :
    |v ⬝ᵥ (D *ᵥ v)| ≤ ‖matrixEntries D‖ * (∑ i, (v i) ^ 2) := by
  rw [← outer_inner, ← outer_norm]
  simpa only [Real.norm_eq_abs] using
    norm_inner_le_norm (𝕜 := ℝ) (matrixEntries D) (matrixEntries (FunctionalInequalities.Analysis.outer v))
omit [DecidableEq ι] in
/-- A floor persists, halved, under a Frobenius perturbation of size at most `a / 2`. -/
theorem FunctionalInequalities.Analysis.quadraticFloor_of_close {S S0 : Matrix ι ι ℝ} {a : ℝ} (hfloor : QuadraticFloor S0 a)
    (hclose : ‖matrixEntries (S - S0)‖ ≤ a / 2) : QuadraticFloor S (a / 2) := by
  intro v
  have hbase := hfloor v
  have hdiff := abs_dotProduct_mulVec_le (S - S0) v
  have hq : v ⬝ᵥ ((S - S0) *ᵥ v) = v ⬝ᵥ (S *ᵥ v) - v ⬝ᵥ (S0 *ᵥ v) := by
    rw [sub_mulVec, dotProduct_sub]
  rw [hq] at hdiff
  have hp : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _hi => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hclose hp
  have hneg := neg_abs_le (v ⬝ᵥ S *ᵥ v - v ⬝ᵥ S0 *ᵥ v)
  nlinarith [hdiff, hmul, hneg]
end Floor
section Sylvester
open Matrix Finset
open scoped RealInnerProductSpace
variable [DecidableEq ι]
theorem FunctionalInequalities.Analysis.root_difference_le_div (S T : Matrix ι ι ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hS : QuadraticFloor S a) (hT : QuadraticFloor T b)
    (hSym : ∀ i j, T i j = T j i) :
    ‖matrixEntries (S - T)‖ ≤ ‖matrixEntries (S * S - T * T)‖ / (a + b) := by
  apply (le_div_iff₀ (add_pos ha hb)).mpr
  simpa only [mul_comm] using root_difference_bound_readable S T hS hT hSym
end Sylvester
end
end
end

noncomputable section
open scoped MatrixOrder RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section LocalLipschitz
open Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal ContDiff
private theorem FunctionalInequalities.Analysis.continuousOn_matrix_sqrt :
    ContinuousOn (CFC.sqrt : Matrix ι ι ℝ → Matrix ι ι ℝ) {M | 0 ≤ M} := CFC.continuousOn_sqrt
/-- **Local Lipschitz property of the canonical matrix square root** along a positive definite profile `M`,
in the Frobenius norm: continuity of `CFC.sqrt` on the nonnegative cone gives a neighbourhood with a common
positive floor, and the Sylvester estimate converts the Lipschitz estimate of `M` into one for `√M`. No
regularity of the root is assumed. -/
theorem solution {X : Type*} [PseudoMetricSpace X]
    (M : X → Matrix ι ι ℝ) (hM : Continuous M) (hPD : ∀ x, (M x).PosDef)
    (hInput : LocallyLipschitz (fun x => FunctionalInequalities.Analysis.matrixEntries (M x))) :
    LocallyLipschitz (fun x => FunctionalInequalities.Analysis.matrixEntries (CFC.sqrt (M x))) := by
  have hroot : Continuous (fun x => CFC.sqrt (M x)) :=
    FunctionalInequalities.Analysis.continuousOn_matrix_sqrt.comp_continuous hM (fun x => (hPD x).posSemidef.nonneg)
  have hE : Continuous (fun x => FunctionalInequalities.Analysis.matrixEntries (CFC.sqrt (M x))) :=
    FunctionalInequalities.Analysis.continuous_matrixEntries.comp hroot
  intro x0
  have hp0 : (CFC.sqrt (M x0)).PosDef :=
    (IsStrictlyPositive.sqrt _ (hPD x0).isStrictlyPositive).posDef
  obtain ⟨a, ha, hfloor⟩ := FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef_readable hp0
  have hclose : ∀ᶠ x in 𝓝 x0,
      ‖FunctionalInequalities.Analysis.matrixEntries (CFC.sqrt (M x) - CFC.sqrt (M x0))‖ < a / 2 := by
    have h := (hE.continuousAt (x := x0)).eventually
      (Metric.ball_mem_nhds (FunctionalInequalities.Analysis.matrixEntries (CFC.sqrt (M x0))) (half_pos ha))
    simpa only [Metric.mem_ball, dist_eq_norm, FunctionalInequalities.Analysis.matrixEntries_sub] using h
  obtain ⟨K, U, hU, hK⟩ := hInput x0
  let V := U ∩ {x | ‖FunctionalInequalities.Analysis.matrixEntries (CFC.sqrt (M x) - CFC.sqrt (M x0))‖ < a / 2}
  have hV : V ∈ 𝓝 x0 := inter_mem hU hclose
  have hf (x : X) (hx : x ∈ V) : FunctionalInequalities.Analysis.QuadraticFloor (CFC.sqrt (M x)) (a / 2) :=
    FunctionalInequalities.Analysis.quadraticFloor_of_close hfloor hx.2.le
  refine ⟨K / (NNReal.mk a ha.le), V, hV, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hSym : ∀ i j, CFC.sqrt (M y) i j = CFC.sqrt (M y) j i := by
    intro i j
    simpa only [star_trivial] using
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M y))).isHermitian.apply j i
  have hbound := FunctionalInequalities.Analysis.root_difference_le_div (CFC.sqrt (M x)) (CFC.sqrt (M y))
    (half_pos ha) (half_pos ha) (hf x hx) (hf y hy) hSym
  rw [CFC.sqrt_mul_sqrt_self _ (hPD x).posSemidef.nonneg,
    CFC.sqrt_mul_sqrt_self _ (hPD y).posSemidef.nonneg] at hbound
  have harg := hK.dist_le_mul x hx.1 y hy.1
  have hsum : a / 2 + a / 2 = a := by ring
  rw [hsum] at hbound
  simp only [dist_eq_norm, ← FunctionalInequalities.Analysis.matrixEntries_sub] at harg ⊢
  have hc : ((K / (NNReal.mk a ha.le) : ℝ≥0) : ℝ) = (K : ℝ) / a := rfl
  rw [hc]
  calc
    ‖FunctionalInequalities.Analysis.matrixEntries (CFC.sqrt (M x) - CFC.sqrt (M y))‖ ≤ ‖FunctionalInequalities.Analysis.matrixEntries (M x - M y)‖ / a := hbound
    _ ≤ ((K : ℝ) * dist x y) / a := div_le_div_of_nonneg_right harg ha.le
    _ = ((K : ℝ) / a) * dist x y := by ring
