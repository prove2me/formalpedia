-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.sum_integral_spectral_noise_energy_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:42.255022+00:00
-- url     : https://prove2.me/submissions/a2ecde37-8fdb-41c4-9872-ab659ed11929

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_QuadraticAction
import Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_mul_of_mean_one_readable
import Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_spectral_geometry_readable

section
open Matrix
noncomputable section
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem FunctionalInequalities.Analysis.trace_transpose_mul_shift_one (A : Matrix ι ι ℝ) (t : ℝ) :
    Matrix.trace ((A + t • 1).transpose * (A + t • 1)) =
      Matrix.trace (A.transpose*A) + 2*t*Matrix.trace A + (Fintype.card ι : ℝ)*t^2 := by
  simp only [Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_one,
    Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
    Matrix.trace_add,Matrix.trace_smul,Matrix.trace_transpose,Matrix.trace_one,smul_eq_mul]
  ring
theorem FunctionalInequalities.Analysis.trace_transpose_mul_right_involution (A Q : Matrix ι ι ℝ)
    (hQ : Q.IsSymm) (hQQ : Q*Q=1) :
    Matrix.trace ((A*Q).transpose*(A*Q)) = Matrix.trace (A.transpose*A) := by
  rw [Matrix.transpose_mul,hQ]
  calc
    Matrix.trace (Q * A.transpose * (A*Q)) = Matrix.trace ((A.transpose*A*Q)*Q) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Q (A.transpose*A*Q)
    _ = Matrix.trace (A.transpose*A) := by
      rw [Matrix.mul_assoc, hQQ,Matrix.mul_one]
omit [DecidableEq ι] in
theorem FunctionalInequalities.Analysis.trace_symmetric_conjugation (S H : Matrix ι ι ℝ) :
    Matrix.trace (S*H*S) = Matrix.trace ((S*S)*H) := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle S H S
omit [DecidableEq ι] in
theorem FunctionalInequalities.Analysis.trace_transpose_conjugation_sq (S H : Matrix ι ι ℝ)
    (hS : S.IsSymm) (hH : H.IsSymm) :
    Matrix.trace ((S*H*S).transpose*(S*H*S)) = Matrix.trace ((S*S)*H*(S*S)*H) := by
  have hSt : S.transpose=S := hS
  have hHt : H.transpose=H := hH
  have ht : (S*H*S).transpose = S*H*S := by
    simp only [Matrix.transpose_mul,hSt,hHt,Matrix.mul_assoc]
  rw [ht]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (S*H*S*S*H) S
end
end
end

section
open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace Topology ContDiff Matrix.Norms.Frobenius
noncomputable section
section
/-- Measurability of `x ↦ τ(x) v`. -/
theorem FunctionalInequalities.Probability.Stein.action_measurable {X : Type*} [MeasurableSpace X] {n : ℕ}
    {τ : X → KernelMatrix n} (hτ : ∀ i j, Measurable (fun x => τ x i j)) (v : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun x => action (τ x) v) := by
  apply (WithLp.measurable_toLp 2 _).comp
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun x => ∑ j, τ x i j * v j)
  exact Finset.measurable_sum _ (fun j _ =>
    (hτ i j).mul measurable_const)
end
end
noncomputable section
open scoped RealInnerProductSpace
section
theorem FunctionalInequalities.Probability.Stein.action_mul {n : ℕ} (A B : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (A*B) x = action A (action B x) := by
  apply WithLp.ofLp_injective
  exact (Matrix.mulVec_mulVec x.ofLp A B).symm
theorem FunctionalInequalities.Probability.Stein.action_add {n : ℕ} (A B : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (A+B) x = action A x + action B x := by
  apply WithLp.ofLp_injective
  exact Matrix.add_mulVec A B x.ofLp
theorem FunctionalInequalities.Probability.Stein.action_smul {n : ℕ} (t : ℝ) (A : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (t • A) x = t • action A x := by
  apply WithLp.ofLp_injective
  exact Matrix.smul_mulVec t A x.ofLp
theorem FunctionalInequalities.Probability.Stein.action_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    action (1 : KernelMatrix n) x = x := by
  apply WithLp.ofLp_injective
  exact Matrix.one_mulVec x.ofLp
theorem FunctionalInequalities.Probability.Stein.action_basis_apply {n : ℕ} (A : KernelMatrix n) (i j : Fin n) :
    action A (EuclideanSpace.basisFun (Fin n) ℝ i) j = A j i := by
  rw [EuclideanSpace.basisFun_apply]
  change (A.mulVec (Pi.single i 1)) j = A j i
  rw [Matrix.mulVec_single_one]
  rfl
theorem FunctionalInequalities.Probability.Stein.sum_norm_action_basis_sq_eq_trace_transpose_mul {n : ℕ} (A : KernelMatrix n) :
    (∑ i, ‖action A (EuclideanSpace.basisFun (Fin n) ℝ i)‖^2) = Matrix.trace (A.transpose*A) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  simp only [action_basis_apply,Matrix.trace,Matrix.diag_apply,
    Matrix.mul_apply,Matrix.transpose_apply,pow_two]
end
end
end

noncomputable section
open scoped RealInnerProductSpace MatrixOrder
open FunctionalInequalities.Probability.Stein
section
set_option maxHeartbeats 800000 in
theorem FunctionalInequalities.Analysis.sum_norm_action_spectral_sign_noise {n : ℕ}
    (M H : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hH : H.IsSymm)
    (hunit : IsUnit M) (t : ℝ) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M * M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    (∑ i : Fin n, ‖action (S * H * S + t • (1 : Matrix (Fin n) (Fin n) ℝ))
      (action Q (EuclideanSpace.single i 1))‖ ^ 2) =
      Matrix.trace (B * H * B * H) + 2 * t * Matrix.trace (B * H) + (n : ℝ) * t ^ 2 := by
  let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
  let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
  change (∑ i : Fin n, ‖action (S*H*S + t • (1 : Matrix (Fin n) (Fin n) ℝ))
    (action Q (EuclideanSpace.single i 1))‖ ^ 2) =
    Matrix.trace (B*H*B*H) + 2*t*Matrix.trace (B*H) + (n : ℝ)*t^2
  obtain ⟨_,hSp,hQ,_,hSS,_,hQQ,_,_,_,_,_⟩ := symmetric_matrix_spectral_geometry_readable M hM hunit
  have hS : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp hSp.isHermitian
  have hb (i : Fin n) : EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin n) ℝ i :=
    by rw [EuclideanSpace.basisFun_apply]
  simp_rw [hb, ← action_mul]
  rw [sum_norm_action_basis_sq_eq_trace_transpose_mul,
    trace_transpose_mul_right_involution _ Q hQ hQQ, trace_transpose_mul_shift_one,
    trace_transpose_conjugation_sq S H hS hH, trace_symmetric_conjugation S H, hSS]
  simp only [Fintype.card_fin, B]
end
end
noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace MatrixOrder
set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} {Ω Δ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Δ] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (γ : Measure Δ) [IsProbabilityMeasure γ]
    (H : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hHmeas : ∀ i j, Measurable (fun y => H y i j))
    (hHsym : ∀ᵐ y ∂ρ, (H y).IsSymm)
    (hHint : ∀ i j, Integrable (fun y => H y i j) ρ)
    (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hT25 : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
      Integrable (fun y => Matrix.trace (B*H y*B*H y)) ρ ∧
        (∫ y, Matrix.trace (B*H y*B*H y) ∂ρ) ≤ 2*Matrix.trace (B*B))
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) (t : ℝ) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    (∀ i : Fin n, Integrable (fun y => ‖FunctionalInequalities.Probability.Stein.action (S*H y*S + t • 1)
      (FunctionalInequalities.Probability.Stein.action Q (EuclideanSpace.single i 1))‖^2) ρ) ∧
    (∑ i : Fin n, ∫ p : Ω × Δ, ‖FunctionalInequalities.Probability.Stein.action (S*H p.1*S + t • 1)
      (FunctionalInequalities.Probability.Stein.action Q (EuclideanSpace.single i 1))‖^2 ∂ρ.prod γ) ≤
      2*Matrix.trace (M*M) + 2*t*Matrix.trace B + (n : ℝ)*t^2 := by
  let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
  let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
  let F : Fin n → Ω → ℝ := fun i y => ‖FunctionalInequalities.Probability.Stein.action (S*H y*S + t • 1)
    (FunctionalInequalities.Probability.Stein.action Q (EuclideanSpace.single i 1))‖^2
  let D : Ω → ℝ := fun y => Matrix.trace (B*H y*B*H y) +
    2*t*Matrix.trace (B*H y) + (n : ℝ)*t^2
  obtain ⟨hBp,_,_,hBB,_,_,_,_,_,_,_,_⟩ := FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry_readable M hM hunit
  have hB : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hBp.isHermitian
  obtain ⟨hEint,hEb⟩ := hT25 B hB
  obtain ⟨hTrint,hTr⟩ := FunctionalInequalities.Analysis.integral_trace_mul_of_mean_one_readable ρ H hHint hmean B
  have hlin : Integrable (fun y => 2*t*Matrix.trace (B*H y)) ρ := hTrint.const_mul (2*t)
  have hcon : Integrable (fun _ : Ω => (n : ℝ)*t^2) ρ := integrable_const _
  have hD : Integrable D ρ := (hEint.add hlin).add hcon
  have hFmeas (i : Fin n) : Measurable (F i) := by
    have hv := FunctionalInequalities.Probability.Stein.action_measurable hHmeas (FunctionalInequalities.Probability.Stein.action S (FunctionalInequalities.Probability.Stein.action Q (EuclideanSpace.single i 1)))
    have hs := (Matrix.toEuclideanLin S).toContinuousLinearMap.continuous.measurable.comp hv
    have hvec := hs.add (measurable_const (a := t • FunctionalInequalities.Probability.Stein.action Q (EuclideanSpace.single i 1)))
    dsimp only [F]
    simp_rw [FunctionalInequalities.Probability.Stein.action_add,FunctionalInequalities.Probability.Stein.action_smul,FunctionalInequalities.Probability.Stein.action_one,FunctionalInequalities.Probability.Stein.action_mul]
    exact hvec.norm.pow_const 2
  have heq : (fun y => ∑ i, F i y) =ᵐ[ρ] D := by
    filter_upwards [hHsym] with y hy
    exact FunctionalInequalities.Analysis.sum_norm_action_spectral_sign_noise M (H y) hM hy hunit t
  have hsumInt : Integrable (fun y => ∑ i, F i y) ρ := hD.congr heq.symm
  have hFi (i : Fin n) : Integrable (F i) ρ := by
    apply hsumInt.mono' (hFmeas i).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    change F i y ≤ ∑ j, F j y
    exact Finset.single_le_sum (fun j _ => show 0 ≤ F j y from sq_nonneg _) (Finset.mem_univ i)
  have hsum : (∑ i, ∫ y, F i y ∂ρ) = ∫ y, D y ∂ρ := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hFi i)]
    exact integral_congr_ae heq
  have hDint : (∫ y, D y ∂ρ) =
      (∫ y, Matrix.trace (B*H y*B*H y) ∂ρ) + 2*t*Matrix.trace B + (n : ℝ)*t^2 := by
    calc
      _ = (∫ y, Matrix.trace (B*H y*B*H y) + 2*t*Matrix.trace (B*H y) ∂ρ) +
          ∫ _ : Ω, (n : ℝ)*t^2 ∂ρ := integral_add (hEint.add hlin) hcon
      _ = ((∫ y, Matrix.trace (B*H y*B*H y) ∂ρ) +
          ∫ y, 2*t*Matrix.trace (B*H y) ∂ρ) + ∫ _ : Ω, (n : ℝ)*t^2 ∂ρ :=
        congrArg (fun z => z + ∫ _ : Ω, (n : ℝ)*t^2 ∂ρ) (integral_add hEint hlin)
      _ = _ := by
        rw [integral_const_mul,hTr]
        simp only [integral_const,probReal_univ,one_smul]
  have hproj : MeasurePreserving (Prod.fst : Ω × Δ → Ω) (ρ.prod γ) ρ := measurePreserving_fst
  have hprod (i : Fin n) : (∫ p : Ω × Δ, F i p.1 ∂ρ.prod γ) = ∫ y, F i y ∂ρ := by
    calc
      _ = ∫ y, F i y ∂(Measure.map Prod.fst (ρ.prod γ)) :=
        (integral_map hproj.measurable.aemeasurable ((hFi i).aestronglyMeasurable.mono_measure hproj.map_eq.le)).symm
      _ = _ := by rw [hproj.map_eq]
  change (∀ i, Integrable (F i) ρ) ∧ (∑ i, ∫ p : Ω × Δ, F i p.1 ∂ρ.prod γ) ≤ _
  refine ⟨hFi,?_⟩
  simp_rw [hprod]
  rw [hsum,hDint]
  have hBB' : B*B=M*M := hBB
  rw [hBB'] at hEb
  dsimp only [B] at hEb ⊢
  linarith only [hEb]
