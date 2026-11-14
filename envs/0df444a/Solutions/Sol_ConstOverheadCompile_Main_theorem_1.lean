-- Prove2me | solution 1 for ConstOverheadCompile.Main.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T22:17:25.450192+00:00
-- url     : https://prove2.me/submissions/f08c9435-8c2b-436f-96f8-16c9f56fefe5

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_AdaptiveCircuit
import Theorems.Thm_ConstOverheadCompile_Main_decomposition_cnot_h_rotation
import Theorems.Thm_ConstOverheadCompile_Main_theorem_9

open scoped Kronecker Matrix

/-!
# Step 1: Hermitian Trace-Norm, Trace-Distance, and Density-Operator Lemmas
-/

section Step1Scope

open scoped MatrixOrder ComplexOrder

section Step1Helpers

private lemma step1_unitary_mul_conjTranspose {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U * Uᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU

private lemma step1_unitary_conjTranspose_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Uᴴ * U = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

private lemma step1_unitary_conjTranspose_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  exact step1_unitary_conjTranspose_mul hU

private lemma step1_trace_conj_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) (D : Matrix ι ι ℂ) :
    (U * D * Uᴴ).trace = D.trace := by
  rw [Matrix.trace_mul_cycle, step1_unitary_conjTranspose_mul hU, one_mul]

private lemma step1_hermitian_spectral {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [hX.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

private lemma step1_conj_diag_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (s : ι → ℂ)
    (hs : ∀ i, s i * star (s i) = 1) :
    U * Matrix.diagonal s * Uᴴ ∈ Matrix.unitaryGroup ι ℂ := by
  have hs_diag : Matrix.diagonal s * (Matrix.diagonal s)ᴴ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    simp only [Pi.star_apply, hs i]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (U * Matrix.diagonal s * Uᴴ) * (U * ((Matrix.diagonal s)ᴴ * Uᴴ))
      = U * (Matrix.diagonal s * (Uᴴ * U) * (Matrix.diagonal s)ᴴ) * Uᴴ := by
          simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal s * (Matrix.diagonal s)ᴴ) * Uᴴ := by
          rw [step1_unitary_conjTranspose_mul hU, Matrix.mul_one]
    _ = U * Uᴴ := by rw [hs_diag, Matrix.mul_one]
    _ = 1 := step1_unitary_mul_conjTranspose hU

private lemma step1_conj_diag_mul_conj_diag {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (d₁ d₂ : ι → ℂ) :
    (U * Matrix.diagonal d₁ * Uᴴ) * (U * Matrix.diagonal d₂ * Uᴴ) =
      U * Matrix.diagonal (fun i => d₁ i * d₂ i) * Uᴴ := by
  calc (U * Matrix.diagonal d₁ * Uᴴ) * (U * Matrix.diagonal d₂ * Uᴴ)
      = U * (Matrix.diagonal d₁ * (Uᴴ * U) * Matrix.diagonal d₂) * Uᴴ := by
          simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal d₁ * Matrix.diagonal d₂) * Uᴴ := by
          rw [step1_unitary_conjTranspose_mul hU, Matrix.mul_one]
    _ = U * Matrix.diagonal (fun i => d₁ i * d₂ i) * Uᴴ := by
          rw [Matrix.diagonal_mul_diagonal]

private lemma step1_traceNorm_eq_sum_abs_eigenvalues {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    WildeQIT.traceNorm X = ∑ i : ι, |hX.eigenvalues i| := by
  have h1 : CFC.sqrt (Xᴴ * X) = CFC.abs X := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  have h2 : CFC.abs X = cfc (fun r : ℝ => ‖r‖) X :=
    CFC.abs_eq_cfc_norm X (Matrix.isHermitian_iff_isSelfAdjoint.mp hX)
  have h3 : cfc (fun r : ℝ => ‖r‖) X = hX.cfc (fun r : ℝ => ‖r‖) :=
    Matrix.IsHermitian.cfc_eq hX _
  have h4 : (hX.cfc (fun r : ℝ => ‖r‖)).trace = ∑ i : ι, ((|hX.eigenvalues i| : ℝ) : ℂ) := by
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rw [step1_trace_conj_unitary hX.eigenvectorUnitary.prop, Matrix.trace_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, Real.norm_eq_abs]
    rfl
  unfold WildeQIT.traceNorm
  rw [h1, h2, h3, h4, Complex.re_sum]
  simp only [Complex.ofReal_re]

private lemma step1_traceNorm_eq_trace_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    ∃ S ∈ Matrix.unitaryGroup ι ℂ, WildeQIT.traceNorm X = (Matrix.trace (S * X)).re := by
  let s : ι → ℂ := fun i => if 0 ≤ hX.eigenvalues i then 1 else -1
  let U : Matrix ι ι ℂ := hX.eigenvectorUnitary
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := hX.eigenvectorUnitary.prop
  have hS : U * Matrix.diagonal s * Uᴴ ∈ Matrix.unitaryGroup ι ℂ :=
    step1_conj_diag_unitary U hU s fun i => by dsimp [s]; split_ifs <;> simp
  refine ⟨U * Matrix.diagonal s * Uᴴ, hS, ?_⟩
  have hdiag : (fun i => s i * (hX.eigenvalues i : ℂ)) =
      (fun i => ((|hX.eigenvalues i| : ℝ) : ℂ)) := by
    ext i
    dsimp [s]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; push_cast; ring
  have hSX : (U * Matrix.diagonal s * Uᴴ) * X =
      U * Matrix.diagonal (fun i => ((|hX.eigenvalues i| : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rhs; rw [step1_hermitian_spectral hX]
    rw [step1_conj_diag_mul_conj_diag U hU s (fun i => (hX.eigenvalues i : ℂ)), hdiag]
  rw [hSX, step1_trace_conj_unitary hU, Matrix.trace_diagonal,
    step1_traceNorm_eq_sum_abs_eigenvalues hX, Complex.re_sum]
  simp only [Complex.ofReal_re]

private lemma step1_unitary_entry_norm_le_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) (i j : ι) :
    ‖W i j‖ ≤ 1 := by
  have h1 : (Wᴴ * W) j j = 1 := by
    rw [step1_unitary_conjTranspose_mul hW, Matrix.one_apply_eq]
  have h2 : ∑ k : ι, ‖W k j‖ ^ 2 = 1 := by
    have h1' : (∑ k : ι, star (W k j) * W k j).re = (1 : ℂ).re := by
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congrArg Complex.re h1
    simp only [Complex.one_re] at h1'
    rw [← h1', Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmul : star (W k j) * W k j = ((‖W k j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [hmul, Complex.ofReal_re]
  have hsq : ‖W i j‖ ^ 2 ≤ 1 := by
    calc ‖W i j‖ ^ 2 ≤ ∑ k : ι, ‖W k j‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ‖W k j‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      _ = 1 := h2
  nlinarith [norm_nonneg (W i j)]

private lemma step1_norm_trace_unitary_mul_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    ‖Matrix.trace (W * X)‖ ≤ WildeQIT.traceNorm X := by
  let U : Matrix ι ι ℂ := hX.eigenvectorUnitary
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := hX.eigenvectorUnitary.prop
  let W' : Matrix ι ι ℂ := Uᴴ * W * U
  have hW' : W' ∈ Matrix.unitaryGroup ι ℂ :=
    mul_mem (mul_mem (step1_unitary_conjTranspose_mem hU) hW) hU
  have htr : Matrix.trace (W * X) =
      ∑ i : ι, W' i i * (hX.eigenvalues i : ℂ) := by
    calc Matrix.trace (W * X)
        = Matrix.trace (W * (U * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) * Uᴴ)) := by
            conv_lhs => rw [step1_hermitian_spectral hX]
      _ = Matrix.trace ((W * U) * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) * Uᴴ) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Uᴴ * (W * U) * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))) := by
            rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (W' * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))) := by
            simp only [W', Matrix.mul_assoc]
      _ = ∑ i : ι, W' i i * (hX.eigenvalues i : ℂ) := by
            simp [Matrix.trace, Matrix.mul_diagonal]
  rw [htr, step1_traceNorm_eq_sum_abs_eigenvalues hX]
  calc ‖∑ i : ι, W' i i * (hX.eigenvalues i : ℂ)‖
      ≤ ∑ i : ι, ‖W' i i * (hX.eigenvalues i : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i : ι, ‖W' i i‖ * |hX.eigenvalues i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ i : ι, 1 * |hX.eigenvalues i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (step1_unitary_entry_norm_le_one hW' i i) (abs_nonneg _)
    _ = ∑ i : ι, |hX.eigenvalues i| := by simp

private lemma step1_re_trace_unitary_mul_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (Matrix.trace (W * X)).re ≤ WildeQIT.traceNorm X :=
  (Complex.re_le_norm _).trans (step1_norm_trace_unitary_mul_le hX hW)

private lemma step1_traceNorm_neg {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    WildeQIT.traceNorm (-A) = WildeQIT.traceNorm A := by
  simp [WildeQIT.traceNorm]

private lemma step1_traceNorm_of_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    WildeQIT.traceNorm A = A.trace.re := by
  have h1 : CFC.sqrt (Aᴴ * A) = CFC.abs A := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  unfold WildeQIT.traceNorm
  rw [h1, CFC.abs_of_nonneg A hA.nonneg]

private lemma step1_posSemidef_list_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    {l : List (Matrix ι ι ℂ)} (hl : ∀ M ∈ l, M.PosSemidef) :
    l.sum.PosSemidef := by
  induction l with
  | nil => simpa using Matrix.PosSemidef.zero
  | cons M ms ih =>
      simp only [List.sum_cons]
      exact (hl M (by simp)).add (ih fun N hN => hl N (by simp [hN]))

private lemma step1_list_map_kraus_sub {ι : Type} [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix ι ι ℂ)) (A B : Matrix ι ι ℂ) :
    (ks.map fun K => K * (A - B) * Kᴴ).sum =
      (ks.map fun K => K * A * Kᴴ).sum - (ks.map fun K => K * B * Kᴴ).sum := by
  induction ks with
  | nil => simp
  | cons K ks ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel

private lemma step1_trace_list_map_kraus {ι : Type} [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    (ks.map fun K => K * A * Kᴴ).sum.trace =
      ((ks.map fun K => Kᴴ * K).sum * A).trace := by
  induction ks with
  | nil => simp
  | cons K ks ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.trace_add, Matrix.add_mul, ih]
      congr 1
      rw [Matrix.trace_mul_cycle]

private lemma step1_trace_mul_conjTranspose_self_re {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    (Matrix.trace (M * Mᴴ)).re = ∑ p : ι × ι, ‖M p.1 p.2‖ ^ 2 := by
  have htr : (Matrix.trace (M * Mᴴ)).re = ∑ i : ι, ∑ j : ι, ‖M i j‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hmul : M i j * star (M i j) = ((‖M i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    rw [hmul, Complex.ofReal_re]
  rw [htr, Fintype.sum_prod_type]

private lemma step1_frobenius_cauchy_schwarz {ι : Type} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) :
    ‖Matrix.trace (P * Qᴴ)‖ ≤
      Real.sqrt (Matrix.trace (P * Pᴴ)).re * Real.sqrt (Matrix.trace (Q * Qᴴ)).re := by
  rw [step1_trace_mul_conjTranspose_self_re P, step1_trace_mul_conjTranspose_self_re Q]
  calc ‖Matrix.trace (P * Qᴴ)‖
      = ‖∑ i : ι, ∑ j : ι, P i j * star (Q i j)‖ := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ = ‖∑ p : ι × ι, P p.1 p.2 * star (Q p.1 p.2)‖ := by
          rw [Fintype.sum_prod_type]
    _ ≤ ∑ p : ι × ι, ‖P p.1 p.2 * star (Q p.1 p.2)‖ := norm_sum_le _ _
    _ = ∑ p : ι × ι, ‖P p.1 p.2‖ * ‖Q p.1 p.2‖ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ p : ι × ι, ‖P p.1 p.2‖ ^ 2) *
          Real.sqrt (∑ p : ι × ι, ‖Q p.1 p.2‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _

private lemma step1_trace_unitary_mul_frobenius {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℂ} (hS : S ∈ Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) :
    (Matrix.trace ((S * M) * (S * M)ᴴ)).re = (Matrix.trace (M * Mᴴ)).re := by
  have h1 : Matrix.trace ((S * M) * (S * M)ᴴ) = Matrix.trace ((S * M)ᴴ * (S * M)) :=
    Matrix.trace_mul_comm _ _
  have h2 : (S * M)ᴴ * (S * M) = Mᴴ * M := by
    calc (S * M)ᴴ * (S * M)
        = Mᴴ * (Sᴴ * S) * M := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * M := by rw [step1_unitary_conjTranspose_mul hS, Matrix.mul_one]
  have h3 : Matrix.trace (Mᴴ * M) = Matrix.trace (M * Mᴴ) := Matrix.trace_mul_comm _ _
  rw [h1, h2, h3]

private lemma step1_normalize_psd_density {ι : Type} [Fintype ι]
    {M ρ₀ : Matrix ι ι ℂ} (hM : M.PosSemidef) (hρ₀ : WildeQIT.IsDensityOperator ρ₀) :
    0 ≤ M.trace.re ∧
      ∃ σ : Matrix ι ι ℂ, WildeQIT.IsDensityOperator σ ∧ M = (M.trace.re : ℂ) • σ := by
  have htr_nonneg : 0 ≤ M.trace := hM.trace_nonneg
  have hre_nonneg : 0 ≤ M.trace.re := (Complex.nonneg_iff.mp htr_nonneg).1
  have him_zero : M.trace.im = 0 := (Complex.nonneg_iff.mp htr_nonneg).2.symm
  have htr_coe : (M.trace.re : ℂ) = M.trace := Complex.ext rfl him_zero.symm
  refine ⟨hre_nonneg, ?_⟩
  by_cases hp : M.trace.re = 0
  · refine ⟨ρ₀, hρ₀, ?_⟩
    have htr0 : M.trace = 0 := by rw [← htr_coe, hp]; simp
    have hM0 : M = 0 := hM.trace_eq_zero_iff.mp htr0
    rw [hp]
    simp [hM0]
  · refine ⟨((M.trace.re⁻¹ : ℝ) : ℂ) • M, ?_, ?_⟩
    · refine ⟨hM.smul (Complex.nonneg_iff.mpr ⟨by simpa using inv_nonneg.mpr hre_nonneg, by simp⟩), ?_⟩
      rw [Matrix.trace_smul, smul_eq_mul, ← htr_coe]
      norm_cast
      exact inv_mul_cancel₀ hp
    · rw [smul_smul]
      have hmul : (M.trace.re : ℂ) * ((M.trace.re⁻¹ : ℝ) : ℂ) = 1 := by
        norm_cast
        exact mul_inv_cancel₀ hp
      rw [hmul, one_smul]

end Step1Helpers

theorem step1_traceDist_self {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    WildeQIT.traceDist A A = 0 := by
  simp [WildeQIT.traceDist, WildeQIT.traceNorm]

theorem step1_traceNorm_add_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    WildeQIT.traceNorm (X + Y) ≤ WildeQIT.traceNorm X + WildeQIT.traceNorm Y := by
  obtain ⟨S, hS, hnorm⟩ := step1_traceNorm_eq_trace_unitary (hX.add hY)
  rw [hnorm, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (step1_re_trace_unitary_mul_le hX hS) (step1_re_trace_unitary_mul_le hY hS)

theorem step1_traceDist_triangle {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B C : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    WildeQIT.traceDist A C ≤ WildeQIT.traceDist A B + WildeQIT.traceDist B C := by
  unfold WildeQIT.traceDist
  have hsub : A - C = (A - B) + (B - C) := by abel
  rw [hsub]
  exact step1_traceNorm_add_le (hA.sub hB) (hB.sub hC)

theorem step1_traceNorm_smul_of_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    {c : ℝ} (hc : 0 ≤ c) {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    WildeQIT.traceNorm ((c : ℂ) • X) = c * WildeQIT.traceNorm X := by
  have hcX : ((c : ℂ) • X).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hX.eq]
  apply le_antisymm
  · obtain ⟨S, hS, hnorm⟩ := step1_traceNorm_eq_trace_unitary hcX
    rw [hnorm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (step1_re_trace_unitary_mul_le hX hS) hc
  · obtain ⟨S, hS, hnorm⟩ := step1_traceNorm_eq_trace_unitary hX
    rw [hnorm]
    calc c * (Matrix.trace (S * X)).re
        = (Matrix.trace (S * ((c : ℂ) • X))).re := by
            rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      _ ≤ WildeQIT.traceNorm ((c : ℂ) • X) := step1_re_trace_unitary_mul_le hcX hS

theorem step1_isDensityOperator_conj_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ U : Matrix ι ι ℂ} (hρ : WildeQIT.IsDensityOperator ρ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    WildeQIT.IsDensityOperator (U * ρ * Uᴴ) := by
  refine ⟨hρ.1.mul_mul_conjTranspose_same U, ?_⟩
  rw [step1_trace_conj_unitary hU, hρ.2]

theorem step1_cptp_traceNorm_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix ι ι ℂ)) (hks : (ks.map fun K => Kᴴ * K).sum = 1)
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    WildeQIT.traceNorm ((ks.map fun K => K * X * Kᴴ).sum) ≤ WildeQIT.traceNorm X := by
  have hXsa : IsSelfAdjoint X := Matrix.isHermitian_iff_isSelfAdjoint.mp hX
  let Xp : Matrix ι ι ℂ := X⁺
  let Xm : Matrix ι ι ℂ := X⁻
  have hXp : Xp.PosSemidef := Matrix.LE.le.posSemidef (CFC.posPart_nonneg X)
  have hXm : Xm.PosSemidef := Matrix.LE.le.posSemidef (CFC.negPart_nonneg X)
  have hsub : Xp - Xm = X := CFC.posPart_sub_negPart X hXsa
  have hadd : Xp + Xm = CFC.abs X := CFC.posPart_add_negPart X hXsa
  let Yp : Matrix ι ι ℂ := (ks.map fun K => K * Xp * Kᴴ).sum
  let Ym : Matrix ι ι ℂ := (ks.map fun K => K * Xm * Kᴴ).sum
  have hYp : Yp.PosSemidef := step1_posSemidef_list_sum fun M hM => by
    rcases List.mem_map.mp hM with ⟨K, _, rfl⟩
    exact hXp.mul_mul_conjTranspose_same K
  have hYm : Ym.PosSemidef := step1_posSemidef_list_sum fun M hM => by
    rcases List.mem_map.mp hM with ⟨K, _, rfl⟩
    exact hXm.mul_mul_conjTranspose_same K
  have hsum : (ks.map fun K => K * X * Kᴴ).sum = Yp + (-Ym) := by
    rw [← hsub, step1_list_map_kraus_sub, sub_eq_add_neg]
  have htr_p : Yp.trace = Xp.trace := by
    dsimp [Yp]
    rw [step1_trace_list_map_kraus, hks, one_mul]
  have htr_m : Ym.trace = Xm.trace := by
    dsimp [Ym]
    rw [step1_trace_list_map_kraus, hks, one_mul]
  have hX_norm : WildeQIT.traceNorm X = Xp.trace.re + Xm.trace.re := by
    have h1 : CFC.sqrt (Xᴴ * X) = CFC.abs X := by
      rw [← Matrix.star_eq_conjTranspose]
      rfl
    unfold WildeQIT.traceNorm
    rw [h1, ← hadd, Matrix.trace_add, Complex.add_re]
  rw [hsum]
  calc WildeQIT.traceNorm (Yp + -Ym)
      ≤ WildeQIT.traceNorm Yp + WildeQIT.traceNorm (-Ym) :=
          step1_traceNorm_add_le hYp.isHermitian hYm.isHermitian.neg
    _ = WildeQIT.traceNorm Yp + WildeQIT.traceNorm Ym := by
          rw [step1_traceNorm_neg]
    _ = Yp.trace.re + Ym.trace.re := by
          rw [step1_traceNorm_of_posSemidef hYp, step1_traceNorm_of_posSemidef hYm]
    _ = Xp.trace.re + Xm.trace.re := by rw [htr_p, htr_m]
    _ = WildeQIT.traceNorm X := hX_norm.symm

theorem step1_traceDist_conj_diag_unitary_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (d₁ d₂ : ι → ℂ) (hd₁ : ∀ i, ‖d₁ i‖ = 1) (hd₂ : ∀ i, ‖d₂ i‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hd : ∀ i, ‖d₁ i - d₂ i‖ ≤ δ)
    {ρ : Matrix ι ι ℂ} (hρ : WildeQIT.IsDensityOperator ρ) :
    WildeQIT.traceDist
      (Matrix.diagonal d₁ * ρ * (Matrix.diagonal d₁)ᴴ)
      (Matrix.diagonal d₂ * ρ * (Matrix.diagonal d₂)ᴴ) ≤ 2 * δ := by
  let D₁ := Matrix.diagonal d₁
  let D₂ := Matrix.diagonal d₂
  let Δ := D₁ * ρ * D₁ᴴ - D₂ * ρ * D₂ᴴ
  have hΔ : Δ.IsHermitian :=
    (hρ.1.mul_mul_conjTranspose_same D₁).isHermitian.sub
      (hρ.1.mul_mul_conjTranspose_same D₂).isHermitian
  obtain ⟨S, hS, hnorm⟩ := step1_traceNorm_eq_trace_unitary hΔ
  unfold WildeQIT.traceDist
  change WildeQIT.traceNorm Δ ≤ 2 * δ
  rw [hnorm]
  let R := CFC.sqrt ρ
  have hR_nonneg : 0 ≤ R := CFC.sqrt_nonneg ρ
  have hR_herm : R.IsHermitian := (Matrix.LE.le.posSemidef hR_nonneg).isHermitian
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
  have hRRH : R * Rᴴ = ρ := by rw [hR_herm.eq, hRR]
  let A := (D₁ - D₂) * R
  let B₁ := D₁ * R
  let B₂ := D₂ * R
  have hΔ_eq : Δ = A * B₁ᴴ + B₂ * Aᴴ := by
    dsimp [Δ, A, B₁, B₂]
    conv_lhs => rw [← hRRH]
    simp only [Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.conjTranspose_sub, Matrix.mul_assoc]
    abel
  have hD₁_u : D₁ᴴ * D₁ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i
    have hmul : (star d₁) i * d₁ i = ((‖d₁ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [hmul, hd₁ i]; simp
  have hD₂_u : D₂ᴴ * D₂ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i
    have hmul : (star d₂) i * d₂ i = ((‖d₂ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [hmul, hd₂ i]; simp
  have hF_R : (Matrix.trace (R * Rᴴ)).re = 1 := by
    rw [hRRH, hρ.2, Complex.one_re]
  have hF_B₁ : (Matrix.trace (B₁ * B₁ᴴ)).re = 1 := by
    have h1 : Matrix.trace (B₁ * B₁ᴴ) = Matrix.trace (B₁ᴴ * B₁) := Matrix.trace_mul_comm _ _
    have h2 : B₁ᴴ * B₁ = Rᴴ * R := by
      dsimp [B₁]
      calc (D₁ * R)ᴴ * (D₁ * R) = Rᴴ * (D₁ᴴ * D₁) * R := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Rᴴ * R := by rw [hD₁_u, Matrix.mul_one]
    rw [h1, h2, Matrix.trace_mul_comm, hF_R]
  have hF_B₂ : (Matrix.trace (B₂ * B₂ᴴ)).re = 1 := by
    have h1 : Matrix.trace (B₂ * B₂ᴴ) = Matrix.trace (B₂ᴴ * B₂) := Matrix.trace_mul_comm _ _
    have h2 : B₂ᴴ * B₂ = Rᴴ * R := by
      dsimp [B₂]
      calc (D₂ * R)ᴴ * (D₂ * R) = Rᴴ * (D₂ᴴ * D₂) * R := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Rᴴ * R := by rw [hD₂_u, Matrix.mul_one]
    rw [h1, h2, Matrix.trace_mul_comm, hF_R]
  have hF_A : (Matrix.trace (A * Aᴴ)).re ≤ δ ^ 2 := by
    rw [step1_trace_mul_conjTranspose_self_re]
    have hA_entry : ∀ i j : ι, A i j = (d₁ i - d₂ i) * R i j := by
      intro i j
      dsimp [A, D₁, D₂]
      rw [Matrix.sub_mul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.diagonal_mul, sub_mul]
    calc ∑ p : ι × ι, ‖A p.1 p.2‖ ^ 2
        = ∑ p : ι × ι, ‖d₁ p.1 - d₂ p.1‖ ^ 2 * ‖R p.1 p.2‖ ^ 2 := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hA_entry, norm_mul, mul_pow]
      _ ≤ ∑ p : ι × ι, δ ^ 2 * ‖R p.1 p.2‖ ^ 2 := by
            refine Finset.sum_le_sum fun p _ => ?_
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            exact pow_le_pow_left₀ (norm_nonneg _) (hd p.1) 2
      _ = δ ^ 2 * ∑ p : ι × ι, ‖R p.1 p.2‖ ^ 2 := by rw [← Finset.mul_sum]
      _ = δ ^ 2 * (Matrix.trace (R * Rᴴ)).re := by
            rw [← step1_trace_mul_conjTranspose_self_re]
      _ = δ ^ 2 := by rw [hF_R, mul_one]
  have hsqrt_A : Real.sqrt (Matrix.trace (A * Aᴴ)).re ≤ δ := by
    calc Real.sqrt (Matrix.trace (A * Aᴴ)).re
        ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hF_A
      _ = δ := Real.sqrt_sq hδ
  have hterm1 : ‖Matrix.trace ((S * A) * B₁ᴴ)‖ ≤ δ := by
    calc ‖Matrix.trace ((S * A) * B₁ᴴ)‖
        ≤ Real.sqrt (Matrix.trace ((S * A) * (S * A)ᴴ)).re *
            Real.sqrt (Matrix.trace (B₁ * B₁ᴴ)).re :=
            step1_frobenius_cauchy_schwarz (S * A) B₁
      _ = Real.sqrt (Matrix.trace (A * Aᴴ)).re * 1 := by
            rw [step1_trace_unitary_mul_frobenius hS, hF_B₁, Real.sqrt_one]
      _ ≤ δ := by simpa using hsqrt_A
  have hterm2 : ‖Matrix.trace ((S * B₂) * Aᴴ)‖ ≤ δ := by
    calc ‖Matrix.trace ((S * B₂) * Aᴴ)‖
        ≤ Real.sqrt (Matrix.trace ((S * B₂) * (S * B₂)ᴴ)).re *
            Real.sqrt (Matrix.trace (A * Aᴴ)).re :=
            step1_frobenius_cauchy_schwarz (S * B₂) A
      _ = 1 * Real.sqrt (Matrix.trace (A * Aᴴ)).re := by
            rw [step1_trace_unitary_mul_frobenius hS, hF_B₂, Real.sqrt_one]
      _ ≤ δ := by simpa using hsqrt_A
  have htr_SΔ : Matrix.trace (S * Δ) = Matrix.trace ((S * A) * B₁ᴴ) + Matrix.trace ((S * B₂) * Aᴴ) := by
    rw [hΔ_eq, Matrix.mul_add, Matrix.trace_add]
    congr 2
    · exact (Matrix.mul_assoc S A B₁ᴴ).symm
    · exact (Matrix.mul_assoc S B₂ Aᴴ).symm
  calc (Matrix.trace (S * Δ)).re
      ≤ ‖Matrix.trace (S * Δ)‖ := Complex.re_le_norm _
    _ = ‖Matrix.trace ((S * A) * B₁ᴴ) + Matrix.trace ((S * B₂) * Aᴴ)‖ := by rw [htr_SΔ]
    _ ≤ ‖Matrix.trace ((S * A) * B₁ᴴ)‖ + ‖Matrix.trace ((S * B₂) * Aᴴ)‖ := norm_add_le _ _
    _ ≤ δ + δ := add_le_add hterm1 hterm2
    _ = 2 * δ := by ring

theorem step1_proj_decomp_density {m n : ℕ} (q : Fin n)
    {ρ : Matrix (Fin m × QAlgorithms.Qubits n) (Fin m × QAlgorithms.Qubits n) ℂ}
    (hρ : WildeQIT.IsDensityOperator ρ) :
    ∃ (pf pt : ℝ)
      (ρf ρt : Matrix (Fin m × QAlgorithms.Qubits n) (Fin m × QAlgorithms.Qubits n) ℂ),
      0 ≤ pf ∧ 0 ≤ pt ∧ pf + pt = 1 ∧
      WildeQIT.IsDensityOperator ρf ∧ WildeQIT.IsDensityOperator ρt ∧
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q false) * ρ *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q false)ᴴ =
        (pf : ℂ) • ρf ∧
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q true) * ρ *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q true)ᴴ =
        (pt : ℂ) • ρt := by
  let Pf := (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q false
  let Pt := (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q true
  let Mf := Pf * ρ * Pfᴴ
  let Mt := Pt * ρ * Ptᴴ
  have hMf : Mf.PosSemidef := hρ.1.mul_mul_conjTranspose_same Pf
  have hMt : Mt.PosSemidef := hρ.1.mul_mul_conjTranspose_same Pt
  obtain ⟨hpf, ρf, hρf, hMf_eq⟩ := step1_normalize_psd_density hMf hρ
  obtain ⟨hpt, ρt, hρt, hMt_eq⟩ := step1_normalize_psd_density hMt hρ
  have hproj_herm : ∀ b : Bool,
      (ConstOverheadCompile.Main.AdaptiveCircuit.proj q b)ᴴ =
        ConstOverheadCompile.Main.AdaptiveCircuit.proj q b := by
    intro b
    unfold ConstOverheadCompile.Main.AdaptiveCircuit.proj
    rw [Matrix.diagonal_conjTranspose]
    congr 1; ext x
    by_cases h : x q = b <;> simp [h]
  have hproj_idem : ∀ b : Bool,
      ConstOverheadCompile.Main.AdaptiveCircuit.proj q b *
        ConstOverheadCompile.Main.AdaptiveCircuit.proj q b =
        ConstOverheadCompile.Main.AdaptiveCircuit.proj q b := by
    intro b
    unfold ConstOverheadCompile.Main.AdaptiveCircuit.proj
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; ext x
    by_cases h : x q = b <;> simp [h]
  have hproj_sum :
      ConstOverheadCompile.Main.AdaptiveCircuit.proj q false +
        ConstOverheadCompile.Main.AdaptiveCircuit.proj q true = 1 := by
    unfold ConstOverheadCompile.Main.AdaptiveCircuit.proj
    rw [Matrix.diagonal_add, ← Matrix.diagonal_one]
    congr 1; ext x
    cases x q <;> simp
  have hPf_sq : Pfᴴ * Pf = Pf := by
    dsimp [Pf]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hproj_herm,
      ← Matrix.mul_kronecker_mul, one_mul, hproj_idem]
  have hPt_sq : Ptᴴ * Pt = Pt := by
    dsimp [Pt]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hproj_herm,
      ← Matrix.mul_kronecker_mul, one_mul, hproj_idem]
  have hsum_id : Pfᴴ * Pf + Ptᴴ * Pt = 1 := by
    rw [hPf_sq, hPt_sq]
    dsimp [Pf, Pt]
    rw [← Matrix.kronecker_add, hproj_sum, Matrix.one_kronecker_one]
  have htr_sum : Mf.trace.re + Mt.trace.re = 1 := by
    have htrC : Mf.trace + Mt.trace = 1 := by
      dsimp [Mf, Mt]
      rw [Matrix.trace_mul_cycle Pf ρ Pfᴴ, Matrix.trace_mul_cycle Pt ρ Ptᴴ,
        ← Matrix.trace_add, ← Matrix.add_mul, hsum_id, one_mul, hρ.2]
    simpa [Complex.add_re] using congrArg Complex.re htrC
  exact ⟨Mf.trace.re, Mt.trace.re, ρf, ρt, hpf, hpt, htr_sum, hρf, hρt, hMf_eq, hMt_eq⟩

end Step1Scope

structure Step1API : Prop where
  traceDist_self : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    WildeQIT.traceDist A A = 0
  traceNorm_add_le : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ},
    X.IsHermitian → Y.IsHermitian →
    WildeQIT.traceNorm (X + Y) ≤ WildeQIT.traceNorm X + WildeQIT.traceNorm Y
  traceDist_triangle : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B C : Matrix ι ι ℂ},
    A.IsHermitian → B.IsHermitian → C.IsHermitian →
    WildeQIT.traceDist A C ≤ WildeQIT.traceDist A B + WildeQIT.traceDist B C
  traceNorm_smul_of_nonneg : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {c : ℝ},
    0 ≤ c → ∀ {X : Matrix ι ι ℂ}, X.IsHermitian →
    WildeQIT.traceNorm ((c : ℂ) • X) = c * WildeQIT.traceNorm X
  isDensityOperator_conj_unitary : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {ρ U : Matrix ι ι ℂ},
    WildeQIT.IsDensityOperator ρ → U ∈ Matrix.unitaryGroup ι ℂ →
    WildeQIT.IsDensityOperator (U * ρ * Uᴴ)
  cptp_traceNorm_le : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix ι ι ℂ)), (ks.map fun K => Kᴴ * K).sum = 1 →
    ∀ {X : Matrix ι ι ℂ}, X.IsHermitian →
    WildeQIT.traceNorm ((ks.map fun K => K * X * Kᴴ).sum) ≤ WildeQIT.traceNorm X
  traceDist_conj_diag_unitary_le : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (d₁ d₂ : ι → ℂ), (∀ i, ‖d₁ i‖ = 1) → (∀ i, ‖d₂ i‖ = 1) →
    ∀ {δ : ℝ}, 0 ≤ δ → (∀ i, ‖d₁ i - d₂ i‖ ≤ δ) →
    ∀ {ρ : Matrix ι ι ℂ}, WildeQIT.IsDensityOperator ρ →
    WildeQIT.traceDist
      (Matrix.diagonal d₁ * ρ * (Matrix.diagonal d₁)ᴴ)
      (Matrix.diagonal d₂ * ρ * (Matrix.diagonal d₂)ᴴ) ≤ 2 * δ
  proj_decomp_density : ∀ {m n : ℕ} (q : Fin n)
    {ρ : Matrix (Fin m × QAlgorithms.Qubits n) (Fin m × QAlgorithms.Qubits n) ℂ},
    WildeQIT.IsDensityOperator ρ →
    ∃ (pf pt : ℝ)
      (ρf ρt : Matrix (Fin m × QAlgorithms.Qubits n) (Fin m × QAlgorithms.Qubits n) ℂ),
      0 ≤ pf ∧ 0 ≤ pt ∧ pf + pt = 1 ∧
      WildeQIT.IsDensityOperator ρf ∧ WildeQIT.IsDensityOperator ρt ∧
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q false) * ρ *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q false)ᴴ =
        (pf : ℂ) • ρf ∧
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q true) * ρ *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q true)ᴴ =
        (pt : ℂ) • ρt

section Step2Helpers

open QAlgorithms ConstOverheadCompile.Main
open scoped ComplexOrder

/-! ### Embedding and circuit helpers -/

private theorem embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (u : Fin k ↪ Fin m) (w : Fin m ↪ Fin n) :
    embedOp (embedOp M u) w = embedOp M (u.trans w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hR : ∀ a : Fin n, a ∉ Set.range (u.trans w) → y a = z a
  · rw [if_pos hR]
    have hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a := by
      intro a ha
      apply hR a
      rintro ⟨c, hc⟩
      exact ha ⟨u c, hc⟩
    have hu : ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b) := by
      intro b hb
      apply hR (w b)
      rintro ⟨c, hc⟩
      exact hb ⟨c, w.injective hc⟩
    rw [if_pos hw]
    change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
      then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = _
    rw [if_pos hu]
  · rw [if_neg hR]
    simp only [not_forall] at hR
    rcases hR with ⟨a, ha, hne⟩
    by_cases haw : a ∈ Set.range w
    · rcases haw with ⟨b, rfl⟩
      have hbu : b ∉ Set.range u := by
        rintro ⟨c, rfl⟩
        exact ha ⟨c, rfl⟩
      by_cases hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a
      · rw [if_pos hw]
        change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
          then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = 0
        rw [if_neg (fun hu => hne (hu b hbu))]
      · rw [if_neg hw]
    · rw [if_neg (fun hw => hne (hw a haw))]

private theorem embedOp_mul {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
          (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x : Qubits n,
          if ∀ a : Fin n, a ∉ Set.range w → y a = x a then
            A (y ∘ w) (x ∘ w) * B (x ∘ w) (z ∘ w) else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · have hxz : ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun a ha =>
          (hyx a ha).symm.trans (hyz a ha)
        rw [if_pos hyx, if_pos hxz, if_pos hyx]
      · rw [if_neg hyx, zero_mul, if_neg hyx]
    rw [hsum, ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun x _ => x ∘ w)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ hx₁ x₂ hx₂ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨b, rfl⟩
          exact congrFun h b
        · exact (hx₁ a ha).symm.trans (hx₂ a ha))
      (fun x' _ => by
        refine ⟨fun a => if h : ∃ b : Fin m, w b = a then x' (Classical.choose h) else y a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha
          have hnot : ¬ ∃ b : Fin m, w b = a := by simpa [Set.mem_range] using ha
          simp [hnot]
        · funext b
          have h : ∃ b' : Fin m, w b' = w b := ⟨b, rfl⟩
          simp only [Function.comp_apply, h, ↓reduceDIte]
          exact congrArg x' (w.injective (Classical.choose_spec h)))
      (fun _ _ => rfl)
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have hxz : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz (fun a ha => (hyx a ha).trans (hxz a ha))
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

private theorem embedOp_conjTranspose {m n : ℕ} (M : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp Mᴴ w = (embedOp M w)ᴴ := by
  ext y z
  simp only [embedOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range w → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w → z a = y a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (mt hiff.mpr h), star_zero]

private theorem embedOp_isUnitary {m n : ℕ} {M : Matrix (Qubits m) (Qubits m) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Qubits m) ℂ) (w : Fin m ↪ Fin n) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  change M * Mᴴ = 1 at hM
  change embedOp M w * (embedOp M w)ᴴ = 1
  rw [← embedOp_conjTranspose, ← embedOp_mul, hM, embedOp_one]

private theorem kronecker_conjTranspose {α β : Type*}
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp [Matrix.conjTranspose_apply]

private theorem kronecker_one_isUnitary {m n : ℕ} {U : Matrix (Qubits n) (Qubits n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) ∈ Matrix.unitaryGroup (Fin m × Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  change U * Uᴴ = 1 at hU
  change ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U)ᴴ = 1
  rw [kronecker_conjTranspose, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, mul_one, hU, Matrix.one_kronecker_one]

private theorem unitary_nil {S : Set Gate} {n : ℕ} :
    Circuit.unitary ([] : Circuit S n) = 1 := rfl

private theorem unitary_cons {S : Set Gate} {n : ℕ} (g : GateApp S n) (cs : Circuit S n) :
    Circuit.unitary (g :: cs) = Circuit.unitary cs * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

private def liftGateApp {S : Set Gate} {k n : ℕ} (w : Fin k ↪ Fin n)
    (g : GateApp S k) : GateApp S n :=
  ⟨g.gate, g.mem, g.wires.trans w⟩

private def liftCircuit {S : Set Gate} {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : Circuit S k) : Circuit S n :=
  c.map (liftGateApp w)

private theorem liftCircuit_size {S : Set Gate} {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : Circuit S k) : (liftCircuit w c).length = c.length :=
  List.length_map _

private theorem liftCircuit_unitary {S : Set Gate} {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : Circuit S k) :
    (liftCircuit w c).unitary = embedOp c.unitary w := by
  induction c with
  | nil =>
      rw [liftCircuit, List.map_nil, unitary_nil, unitary_nil, embedOp_one]
  | cons g cs ih =>
      dsimp only [liftCircuit]
      rw [List.map_cons, unitary_cons]
      change Circuit.unitary (liftCircuit w cs) *
          embedOp (liftGateApp w g).gate.mat (liftGateApp w g).wires = _
      rw [ih]
      have hg : embedOp (liftGateApp w g).gate.mat (liftGateApp w g).wires =
          embedOp (embedOp g.gate.mat g.wires) w := by
        simpa [liftGateApp] using (embedOp_trans g.gate.mat g.wires w).symm
      rw [hg, ← embedOp_mul, unitary_cons]

private theorem foldr_gate_maxGates {S : Set Gate} {n : ℕ}
    (cs : List (GateApp S n)) (k : AdaptiveCircuit S n) :
    (cs.foldr AdaptiveCircuit.gate k).maxGates = cs.length + k.maxGates := by
  induction cs with
  | nil => simp
  | cons g gs ih =>
      simp [AdaptiveCircuit.maxGates, ih]
      omega

private theorem foldr_gate_krausList {S : Set Gate} {n : ℕ}
    (cs : Circuit S n) (k : AdaptiveCircuit S n) :
    (cs.foldr AdaptiveCircuit.gate k).krausList =
      k.krausList.map (fun K => K * cs.unitary) := by
  induction cs with
  | nil =>
      rw [List.foldr_nil, unitary_nil]
      simp
  | cons g gs ih =>
      simp only [List.foldr_cons, AdaptiveCircuit.krausList, ih, List.map_map]
      refine List.map_congr_left (fun K _ => ?_)
      dsimp only [Function.comp_apply]
      rw [unitary_cons, Matrix.mul_assoc]

/-! ### Part A: Exact expansion from `ArbGates` to `HCnotRotGates` -/

private noncomputable def expandGateCircuit (N : ℕ)
    (hDecomp : ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (Qubits k) (Qubits k) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
        ∃ c : Circuit HCnotRotGates k, c.size ≤ N ∧ c.unitary = U)
    {n : ℕ} (g : GateApp ArbGates n) : Circuit HCnotRotGates n :=
  liftCircuit g.wires (Classical.choose (hDecomp g.gate.arity g.mem.1 g.gate.mat g.mem.2))

private theorem expandGateCircuit_length (N : ℕ)
    (hDecomp : ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (Qubits k) (Qubits k) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
        ∃ c : Circuit HCnotRotGates k, c.size ≤ N ∧ c.unitary = U)
    {n : ℕ} (g : GateApp ArbGates n) :
    (expandGateCircuit N hDecomp g).length ≤ N := by
  dsimp only [expandGateCircuit]
  rw [liftCircuit_size]
  exact (Classical.choose_spec (hDecomp g.gate.arity g.mem.1 g.gate.mat g.mem.2)).1

private theorem expandGateCircuit_unitary (N : ℕ)
    (hDecomp : ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (Qubits k) (Qubits k) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
        ∃ c : Circuit HCnotRotGates k, c.size ≤ N ∧ c.unitary = U)
    {n : ℕ} (g : GateApp ArbGates n) :
    (expandGateCircuit N hDecomp g).unitary = embedOp g.gate.mat g.wires := by
  dsimp only [expandGateCircuit]
  rw [liftCircuit_unitary]
  rw [(Classical.choose_spec (hDecomp g.gate.arity g.mem.1 g.gate.mat g.mem.2)).2]

private noncomputable def expandCircuit (N : ℕ)
    (hDecomp : ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (Qubits k) (Qubits k) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
        ∃ c : Circuit HCnotRotGates k, c.size ≤ N ∧ c.unitary = U)
    {n : ℕ} : AdaptiveCircuit ArbGates n → AdaptiveCircuit HCnotRotGates n
  | .done => .done
  | .gate g k => (expandGateCircuit N hDecomp g).foldr AdaptiveCircuit.gate (expandCircuit N hDecomp k)
  | .measure q k => .measure q (fun b => expandCircuit N hDecomp (k b))

private theorem expandCircuit_maxGates (N : ℕ)
    (hDecomp : ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (Qubits k) (Qubits k) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
        ∃ c : Circuit HCnotRotGates k, c.size ≤ N ∧ c.unitary = U)
    {n : ℕ} (A : AdaptiveCircuit ArbGates n) :
    (expandCircuit N hDecomp A).maxGates ≤ N * A.maxGates := by
  induction A with
  | done => simp [expandCircuit, AdaptiveCircuit.maxGates]
  | gate g k ih =>
      simp only [expandCircuit, AdaptiveCircuit.maxGates, foldr_gate_maxGates]
      have hlen := expandGateCircuit_length N hDecomp g
      calc (expandGateCircuit N hDecomp g).length + (expandCircuit N hDecomp k).maxGates
          ≤ N + N * k.maxGates := Nat.add_le_add hlen ih
        _ = N * (1 + k.maxGates) := by ring
  | measure q k ih =>
      simp only [expandCircuit, AdaptiveCircuit.maxGates]
      exact max_le
        (le_trans (ih false) (Nat.mul_le_mul_left N (le_max_left _ _)))
        (le_trans (ih true) (Nat.mul_le_mul_left N (le_max_right _ _)))

private theorem expandCircuit_krausList (N : ℕ)
    (hDecomp : ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (Qubits k) (Qubits k) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
        ∃ c : Circuit HCnotRotGates k, c.size ≤ N ∧ c.unitary = U)
    {n : ℕ} (A : AdaptiveCircuit ArbGates n) :
    (expandCircuit N hDecomp A).krausList = A.krausList := by
  induction A with
  | done => rfl
  | gate g k ih =>
      simp only [expandCircuit, AdaptiveCircuit.krausList, foldr_gate_krausList, ih,
        expandGateCircuit_unitary]
  | measure q k ih =>
      simp only [expandCircuit, AdaptiveCircuit.krausList, ih false, ih true]

/-! ### Hermitian and channelRef algebraic properties -/

private theorem isHermitian_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (M : Matrix ι ι ℂ) :
    (M * X * Mᴴ).IsHermitian := by
  change (M * X * Mᴴ)ᴴ = M * X * Mᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hX.eq, Matrix.mul_assoc]

private theorem isHermitian_list_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) (hl : ∀ A ∈ l, A.IsHermitian) :
    l.sum.IsHermitian := by
  induction l with
  | nil =>
      change (0 : Matrix ι ι ℂ)ᴴ = 0
      exact Matrix.conjTranspose_zero
  | cons a as ih =>
      simp only [List.sum_cons]
      exact (hl a (List.mem_cons_self)).add (ih (fun x hx => hl x (List.mem_cons_of_mem a hx)))

private theorem isHermitian_finset_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (s : Finset κ) (f : κ → Matrix ι ι ℂ) (hf : ∀ i ∈ s, (f i).IsHermitian) :
    (∑ i ∈ s, f i).IsHermitian := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change (0 : Matrix ι ι ℂ)ᴴ = 0
      exact Matrix.conjTranspose_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private theorem isHermitian_real_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    ((c : ℂ) • X).IsHermitian := by
  change ((c : ℂ) • X)ᴴ = (c : ℂ) • X
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hX.eq]

private theorem channelRef_isHermitian {S : Set Gate} {n : ℕ}
    (B : AdaptiveCircuit S n) (m : ℕ)
    {X : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ} (hX : X.IsHermitian) :
    (B.channelRef m X).IsHermitian := by
  dsimp only [AdaptiveCircuit.channelRef]
  refine isHermitian_list_sum _ ?_
  intro A hA
  rw [List.mem_map] at hA
  rcases hA with ⟨K, _, rfl⟩
  exact isHermitian_conj hX _

private theorem dataChannelRef_isHermitian {S : Set Gate} {n a : ℕ}
    (B : AdaptiveCircuit S (n + a)) (m : ℕ)
    {X : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ} (hX : X.IsHermitian) :
    (B.dataChannelRef m X).IsHermitian := by
  dsimp only [AdaptiveCircuit.dataChannelRef]
  refine isHermitian_finset_sum _ _ ?_
  intro j _
  refine isHermitian_list_sum _ ?_
  intro A hA
  rw [List.mem_map] at hA
  rcases hA with ⟨K, _, rfl⟩
  exact isHermitian_conj hX _

private theorem list_sum_map_sub {α : Type*} {M : Type*} [AddCommGroup M]
    (l : List α) (f g : α → M) :
    (l.map f).sum - (l.map g).sum = (l.map fun x => f x - g x).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons, ← ih]
      abel

private theorem list_sum_map_smul {α : Type*} {M : Type*} [AddCommMonoid M]
    [Module ℂ M] (l : List α) (c : ℂ) (f : α → M) :
    (l.map fun x => c • f x).sum = c • (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, smul_add]

private theorem channelRef_sub {S : Set Gate} {n : ℕ} (B : AdaptiveCircuit S n) (m : ℕ)
    (A C : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    B.channelRef m A - B.channelRef m C = B.channelRef m (A - C) := by
  dsimp only [AdaptiveCircuit.channelRef]
  rw [list_sum_map_sub]
  congr 1
  refine List.map_congr_left (fun K _ => ?_)
  rw [Matrix.mul_sub, Matrix.sub_mul]

private theorem channelRef_smul {S : Set Gate} {n : ℕ} (B : AdaptiveCircuit S n) (m : ℕ)
    (c : ℂ) (A : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    B.channelRef m (c • A) = c • B.channelRef m A := by
  dsimp only [AdaptiveCircuit.channelRef]
  rw [← list_sum_map_smul]
  congr 1
  refine List.map_congr_left (fun K _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul]

private theorem channelRef_gate {S : Set Gate} {n : ℕ}
    (g : GateApp S n) (k : AdaptiveCircuit S n) (m : ℕ)
    (ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    (AdaptiveCircuit.gate g k).channelRef m ρ =
      k.channelRef m
        (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ embedOp g.gate.mat g.wires) * ρ *
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ embedOp g.gate.mat g.wires)ᴴ) := by
  dsimp only [AdaptiveCircuit.channelRef, AdaptiveCircuit.krausList]
  rw [List.map_map]
  congr 1
  refine List.map_congr_left (fun K _ => ?_)
  dsimp only [Function.comp_apply]
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (K * embedOp g.gate.mat g.wires) =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ embedOp g.gate.mat g.wires) := by
    rw [← Matrix.mul_kronecker_mul, one_mul]
  rw [h1, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem channelRef_measure {S : Set Gate} {n : ℕ}
    (q : Fin n) (k : Bool → AdaptiveCircuit S n) (m : ℕ)
    (ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    (AdaptiveCircuit.measure q k).channelRef m ρ =
      (k false).channelRef m
        (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q false) * ρ *
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q false)ᴴ) +
      (k true).channelRef m
        (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q true) * ρ *
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q true)ᴴ) := by
  dsimp only [AdaptiveCircuit.channelRef, AdaptiveCircuit.krausList]
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left (fun K _ => ?_)
    dsimp only [Function.comp_apply]
    have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (K * AdaptiveCircuit.proj q false) =
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) *
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q false) := by
      rw [← Matrix.mul_kronecker_mul, one_mul]
    rw [h1, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · congr 1
    refine List.map_congr_left (fun K _ => ?_)
    dsimp only [Function.comp_apply]
    have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (K * AdaptiveCircuit.proj q true) =
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) *
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q true) := by
      rw [← Matrix.mul_kronecker_mul, one_mul]
    rw [h1, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

/-! ### Unitarity and Kraus completeness -/

private theorem ofMatrix1_isUnitary {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    (Gate.ofMatrix1 M).IsUnitary := by
  rw [Gate.IsUnitary, Matrix.mem_unitaryGroup_iff]
  rw [Matrix.mem_unitaryGroup_iff] at hM
  change M * Mᴴ = 1 at hM
  let e : Qubits 1 ≃ Bool :=
    { toFun := fun b => b 0
      invFun := fun b _ => b
      left_inv := fun b => funext fun i => by rw [Fin.eq_zero i]
      right_inv := fun _ => rfl }
  change (M.submatrix e e) * (M.submatrix e e)ᴴ = 1
  have hsub : (M.submatrix e e)ᴴ = Mᴴ.submatrix e e := rfl
  rw [hsub, Matrix.submatrix_mul_equiv M Mᴴ e e e, hM, Matrix.submatrix_one_equiv]

private theorem ofMatrix2_isUnitary {M : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    (Gate.ofMatrix2 M).IsUnitary := by
  rw [Gate.IsUnitary, Matrix.mem_unitaryGroup_iff]
  rw [Matrix.mem_unitaryGroup_iff] at hM
  change M * Mᴴ = 1 at hM
  let e : Qubits 2 ≃ Bool × Bool :=
    { toFun := fun b => (b 0, b 1)
      invFun := fun p i => if i = 0 then p.1 else p.2
      left_inv := fun b => funext fun i => by fin_cases i <;> rfl
      right_inv := fun p => by simp }
  change (M.submatrix e e) * (M.submatrix e e)ᴴ = 1
  have hsub : (M.submatrix e e)ᴴ = Mᴴ.submatrix e e := rfl
  rw [hsub, Matrix.submatrix_mul_equiv M Mᴴ e e e, hM, Matrix.submatrix_one_equiv]

private theorem hadamard_isUnitary : (Gate.ofMatrix1 hadamard).IsUnitary := by
  apply ofMatrix1_isUnitary
  rw [Matrix.mem_unitaryGroup_iff]
  change hadamard * hadamardᴴ = 1
  have hH : hadamardᴴ = hadamard := by
    ext a b
    cases a <;> cases b <;> simp [hadamard, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  rw [hH, hadamard_mul_self]

private theorem cnot_isUnitary : (Gate.ofMatrix2 cnot).IsUnitary := by
  apply ofMatrix2_isUnitary
  rw [Matrix.mem_unitaryGroup_iff]
  change cnot * cnotᴴ = 1
  have hC : cnotᴴ = cnot := by
    ext p q
    simp only [cnot, Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases hpq : p.1 = q.1 ∧ p.2 = xor q.2 q.1
    · have hqp : q.1 = p.1 ∧ q.2 = xor p.2 p.1 := by
        refine ⟨hpq.1.symm, ?_⟩
        rw [hpq.1, hpq.2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      rw [if_pos hpq, if_pos hqp, star_one]
    · have hqp : ¬ (q.1 = p.1 ∧ q.2 = xor p.2 p.1) := by
        intro h
        apply hpq
        refine ⟨h.1.symm, ?_⟩
        rw [h.1, h.2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      rw [if_neg hpq, if_neg hqp, star_zero]
  rw [hC]
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
    simp [cnot, Matrix.mul_apply, Fintype.sum_prod_type]

private theorem rot_isUnitary (θ : ℝ) : (Gate.ofMatrix1 (rot θ)).IsUnitary := by
  apply ofMatrix1_isUnitary
  rw [Matrix.mem_unitaryGroup_iff]
  change rot θ * (rot θ)ᴴ = 1
  have hdiag : (rot θ)ᴴ = Matrix.diagonal (fun x => if x then star (Complex.exp ((θ : ℂ) * Complex.I)) else 1) := by
    ext x y
    simp only [rot, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : x = y
    · subst h; simp; split_ifs <;> simp
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [hdiag, rot, Matrix.diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    cases a
    · simp
    · simp only [↓reduceIte, Complex.star_def]
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
        Complex.norm_exp_ofReal_mul_I, one_pow, Complex.ofReal_one]
  · simp [h]

private theorem hcnotRotGates_isUnitary : ∀ g ∈ HCnotRotGates, g.IsUnitary := by
  intro g hg
  rcases hg with (rfl | rfl) | ⟨θ, _, rfl⟩
  · exact hadamard_isUnitary
  · exact cnot_isUnitary
  · exact rot_isUnitary θ

private theorem proj_conjTranspose {n : ℕ} (q : Fin n) (b : Bool) :
    (AdaptiveCircuit.proj q b)ᴴ = AdaptiveCircuit.proj q b := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

private theorem proj_mul_self {n : ℕ} (q : Fin n) (b : Bool) :
    AdaptiveCircuit.proj q b * AdaptiveCircuit.proj q b = AdaptiveCircuit.proj q b := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem proj_add {n : ℕ} (q : Fin n) :
    AdaptiveCircuit.proj q false + AdaptiveCircuit.proj q true = 1 := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : y = z
  · subst h; cases y q <;> simp
  · simp [h]

private theorem list_sum_map_mul_left_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) (A B : Matrix ι ι ℂ) :
    (l.map fun K => A * K * B).sum = A * l.sum * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Matrix.mul_add, Matrix.add_mul]

private theorem krausList_sum_conj_mul {S : Set Gate} {n : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary) (B : AdaptiveCircuit S n) :
    (B.krausList.map fun K => Kᴴ * K).sum = 1 := by
  induction B with
  | done =>
      simp [AdaptiveCircuit.krausList]
  | gate g k ih =>
      have hU : embedOp g.gate.mat g.wires ∈ Matrix.unitaryGroup (Qubits n) ℂ :=
        embedOp_isUnitary (hS g.gate g.mem) g.wires
      rw [Matrix.mem_unitaryGroup_iff'] at hU
      change (embedOp g.gate.mat g.wires)ᴴ * embedOp g.gate.mat g.wires = 1 at hU
      simp only [AdaptiveCircuit.krausList, List.map_map]
      have hcongr : (k.krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * embedOp g.gate.mat g.wires)) =
          ((k.krausList.map fun x => xᴴ * x).map fun K =>
            (embedOp g.gate.mat g.wires)ᴴ * K * embedOp g.gate.mat g.wires) := by
        rw [List.map_map]
        refine List.map_congr_left (fun x _ => ?_)
        simp only [Function.comp_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hcongr, list_sum_map_mul_left_right, ih, Matrix.mul_one, hU]
  | measure q k ih =>
      simp only [AdaptiveCircuit.krausList, List.map_append, List.sum_append, List.map_map]
      have hbranch : ∀ b : Bool,
          ((k b).krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * AdaptiveCircuit.proj q b)).sum =
            AdaptiveCircuit.proj q b := by
        intro b
        have hcongr : ((k b).krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * AdaptiveCircuit.proj q b)) =
            (((k b).krausList.map fun x => xᴴ * x).map fun K =>
              (AdaptiveCircuit.proj q b)ᴴ * K * AdaptiveCircuit.proj q b) := by
          rw [List.map_map]
          refine List.map_congr_left (fun x _ => ?_)
          simp only [Function.comp_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [hcongr, list_sum_map_mul_left_right, ih b, Matrix.mul_one,
          proj_conjTranspose, proj_mul_self]
      rw [hbranch false, hbranch true, proj_add]

private theorem list_sum_kronecker_one_left {m n : ℕ}
    (l : List (Matrix (Qubits n) (Qubits n) ℂ)) :
    (l.map fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K).sum =
      (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Matrix.kronecker_add]

private theorem channelRef_kraus_sum_one {S : Set Gate} {n : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary) (B : AdaptiveCircuit S n) (m : ℕ) :
    ((B.krausList.map fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K).map
      fun K => Kᴴ * K).sum = 1 := by
  have h1 : ((B.krausList.map fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K).map
      fun K => Kᴴ * K) =
      ((B.krausList.map fun K => Kᴴ * K).map
        fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left (fun K _ => ?_)
    simp only [Function.comp_apply]
    rw [kronecker_conjTranspose, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, one_mul]
  rw [h1, list_sum_kronecker_one_left, krausList_sum_conj_mul hS B, Matrix.one_kronecker_one]

/-! ### Part B: Grid rounding from `HCnotRotGates` to `CliffordT ∪ gridGates D` -/

private theorem embedOp_of_gate_eq {n : ℕ} {g₁ g₂ : Gate} (h : g₁ = g₂)
    (w₁ : Fin g₁.arity ↪ Fin n) (w₂ : Fin g₂.arity ↪ Fin n)
    (hw : ∀ i : Fin g₂.arity, w₁ (i.cast (congrArg Gate.arity h).symm) = w₂ i) :
    embedOp g₁.mat w₁ = embedOp g₂.mat w₂ := by
  subst h
  have : w₁ = w₂ := DFunLike.ext w₁ w₂ hw
  subst this
  rfl

private theorem embedOp_rot_eq_diagonal {n : ℕ} (α : ℝ) (w : Fin 1 ↪ Fin n) :
    embedOp (Gate.ofMatrix1 (rot α)).mat w =
      Matrix.diagonal (fun x : Qubits n => if x (w 0) then Complex.exp ((α : ℂ) * Complex.I) else 1) := by
  ext y z
  change (if ∀ a : Fin n, a ∉ Set.range w → y a = z a then
      (if y (w 0) = z (w 0) then
        if y (w 0) then Complex.exp ((α : ℂ) * Complex.I) else 1
      else 0)
    else 0) =
    (if y = z then if y (w 0) then Complex.exp ((α : ℂ) * Complex.I) else 1 else 0)
  by_cases hyz : y = z
  · subst hyz
    simp
  · rw [if_neg hyz]
    by_cases h0 : y (w 0) = z (w 0)
    · have hnot : ¬ ∀ a : Fin n, a ∉ Set.range w → y a = z a := by
        intro h
        apply hyz
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨i, rfl⟩
          rw [Fin.eq_zero i]
          exact h0
        · exact h a ha
      rw [if_neg hnot]
    · simp [h0]

private theorem kronecker_one_diagonal {m n : ℕ} (f : Qubits n → ℂ) :
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Matrix.diagonal f) =
      Matrix.diagonal (fun p : Fin m × Qubits n => f p.2) := by
  ext ⟨i₁, y⟩ ⟨i₂, z⟩
  simp only [Matrix.kronecker_apply, Matrix.one_apply, Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases hi : i₁ = i₂ <;> by_cases hy : y = z <;> simp [hi, hy]

private theorem norm_exp_ofReal_mul_I_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have hsq : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ^ 2 ≤ x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.exp_mul_I]
    have hre : (Complex.cos x + Complex.sin x * Complex.I - 1).re = Real.cos x - 1 := by
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    have him : (Complex.cos x + Complex.sin x * Complex.I - 1).im = Real.sin x := by
      simp [Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.sin_ofReal_re]
    rw [Complex.normSq_apply, hre, him]
    have hcos : Real.cos x - 1 = -(2 * Real.sin (x / 2) ^ 2) := by
      have h := Real.cos_two_mul (x / 2)
      rw [show 2 * (x / 2) = x by ring] at h
      have hsc := Real.sin_sq_add_cos_sq (x / 2)
      linarith
    have hsin : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      have h := Real.sin_two_mul (x / 2)
      rw [show 2 * (x / 2) = x by ring] at h
      exact h
    rw [hcos, hsin]
    have hid : (-(2 * Real.sin (x / 2) ^ 2)) * (-(2 * Real.sin (x / 2) ^ 2)) +
        (2 * Real.sin (x / 2) * Real.cos (x / 2)) * (2 * Real.sin (x / 2) * Real.cos (x / 2)) =
        4 * Real.sin (x / 2) ^ 2 * (Real.sin (x / 2) ^ 2 + Real.cos (x / 2) ^ 2) := by ring
    rw [hid, Real.sin_sq_add_cos_sq, mul_one]
    have hsin_le : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
    have hsin_sq : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
      rw [← sq_abs (Real.sin (x / 2)), ← sq_abs (x / 2)]
      exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
    linarith
  nlinarith [norm_nonneg (Complex.exp ((x : ℂ) * Complex.I) - 1), abs_nonneg x, sq_abs x]

private theorem norm_exp_ofReal_mul_I_sub_exp_ofReal_mul_I_le (θ φ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp ((φ : ℂ) * Complex.I)‖ ≤ |θ - φ| := by
  have hfact : Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp ((φ : ℂ) * Complex.I) =
      Complex.exp ((φ : ℂ) * Complex.I) * (Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, Complex.ofReal_sub, ← add_mul, add_sub_cancel]
  rw [hfact, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_exp_ofReal_mul_I_sub_one_le (θ - φ)

private noncomputable def roundGateApp (D : ℕ) (hD : 1 ≤ D) {n : ℕ}
    (g : GateApp HCnotRotGates n) : GateApp (CliffordT ∪ gridGates D) n :=
  letI := Classical.propDecidable
  if h1 : g.gate ∈ ({Gate.ofMatrix1 hadamard, Gate.ofMatrix2 cnot} : Set Gate) then
    ⟨g.gate, Or.inl (by
      rcases h1 with h1' | h1' <;> rw [h1'] <;> simp [CliffordT]), g.wires⟩
  else
    let h2 : ∃ θ : ℝ, θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ g.gate = Gate.ofMatrix1 (rot θ) := by
      rcases g.mem with h | h
      · exact False.elim (h1 h)
      · exact h
    let θ := Classical.choose h2
    let hθ := Classical.choose_spec h2
    let j := Nat.floor ((D : ℝ) * θ / (2 * Real.pi))
    let φ := 2 * Real.pi * (j : ℝ) / (D : ℝ)
    let har : g.gate.arity = 1 := congrArg Gate.arity hθ.2
    let w : Fin 1 ↪ Fin n :=
      ⟨fun i => g.wires (i.cast har.symm), fun i j _ => Subsingleton.elim i j⟩
    ⟨Gate.ofMatrix1 (rot φ), Or.inr ⟨j, by
      have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hD
      have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      have hnonneg : 0 ≤ (D : ℝ) * θ / (2 * Real.pi) :=
        div_nonneg (mul_nonneg hDpos.le hθ.1.1.le) hpi.le
      rw [Nat.floor_lt hnonneg, div_lt_iff₀ hpi, mul_comm (D : ℝ) θ, mul_comm (D : ℝ) (2 * Real.pi)]
      exact mul_lt_mul_of_pos_right hθ.1.2 hDpos, rfl⟩, w⟩

private noncomputable def roundCircuit (D : ℕ) (hD : 1 ≤ D) {n : ℕ} :
    AdaptiveCircuit HCnotRotGates n → AdaptiveCircuit (CliffordT ∪ gridGates D) n
  | .done => .done
  | .gate g k => .gate (roundGateApp D hD g) (roundCircuit D hD k)
  | .measure q k => .measure q (fun b => roundCircuit D hD (k b))

private theorem roundCircuit_maxGates (D : ℕ) (hD : 1 ≤ D) {n : ℕ}
    (A₁ : AdaptiveCircuit HCnotRotGates n) :
    (roundCircuit D hD A₁).maxGates = A₁.maxGates := by
  induction A₁ with
  | done => rfl
  | gate g k ih => simp [roundCircuit, AdaptiveCircuit.maxGates, ih]
  | measure q k ih => simp [roundCircuit, AdaptiveCircuit.maxGates, ih false, ih true]

private theorem roundCircuit_channelRef_close (s1 : Step1API) (D : ℕ) (hD : 1 ≤ D) {n : ℕ}
    (A₁ : AdaptiveCircuit HCnotRotGates n) :
    ∀ (m : ℕ) (ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ),
      WildeQIT.IsDensityOperator ρ →
      WildeQIT.traceDist ((roundCircuit D hD A₁).channelRef m ρ) (A₁.channelRef m ρ) ≤
        4 * Real.pi * (A₁.maxGates : ℝ) / (D : ℝ) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hD
  induction A₁ with
  | done =>
      intro m ρ _
      simp only [AdaptiveCircuit.maxGates, Nat.cast_zero, mul_zero, zero_div]
      have hdone : (roundCircuit D hD (.done : AdaptiveCircuit HCnotRotGates n)).channelRef m ρ =
          (.done : AdaptiveCircuit HCnotRotGates n).channelRef m ρ := rfl
      rw [hdone, s1.traceDist_self]
  | gate g k ih =>
      intro m ρ hρ
      simp only [roundCircuit, AdaptiveCircuit.maxGates]
      rw [channelRef_gate, channelRef_gate]
      by_cases h1 : g.gate ∈ ({Gate.ofMatrix1 hadamard, Gate.ofMatrix2 cnot} : Set Gate)
      · have hg'_eq : roundGateApp D hD g =
            ⟨g.gate, Or.inl (by rcases h1 with h1' | h1' <;> rw [h1'] <;> simp [CliffordT]), g.wires⟩ := by
          dsimp only [roundGateApp]
          rw [dif_pos h1]
        have hUeq : embedOp (roundGateApp D hD g).gate.mat (roundGateApp D hD g).wires =
            embedOp g.gate.mat g.wires := by
          rw [hg'_eq]
        rw [hUeq]
        have hU : ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ embedOp g.gate.mat g.wires) ∈
            Matrix.unitaryGroup (Fin m × Qubits n) ℂ :=
          kronecker_one_isUnitary (embedOp_isUnitary (hcnotRotGates_isUnitary g.gate g.mem) g.wires)
        have hρ' := s1.isDensityOperator_conj_unitary hρ hU
        calc WildeQIT.traceDist
              ((roundCircuit D hD k).channelRef m _)
              (k.channelRef m _)
            ≤ 4 * Real.pi * (k.maxGates : ℝ) / (D : ℝ) := ih m _ hρ'
          _ ≤ 4 * Real.pi * ((1 + k.maxGates : ℕ) : ℝ) / (D : ℝ) := by
              apply div_le_div_of_nonneg_right _ hDpos.le
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact_mod_cast Nat.le_add_left k.maxGates 1
      · have h2 : ∃ θ : ℝ, θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ g.gate = Gate.ofMatrix1 (rot θ) := by
          rcases g.mem with h | h
          · exact False.elim (h1 h)
          · exact h
        let θ := Classical.choose h2
        have hθ : θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ g.gate = Gate.ofMatrix1 (rot θ) :=
          Classical.choose_spec h2
        let j := Nat.floor ((D : ℝ) * θ / (2 * Real.pi))
        let φ := 2 * Real.pi * (j : ℝ) / (D : ℝ)
        let har : g.gate.arity = 1 := congrArg Gate.arity hθ.2
        let w : Fin 1 ↪ Fin n :=
          ⟨fun i => g.wires (i.cast har.symm), fun i j _ => Subsingleton.elim i j⟩
        have hg_op : embedOp g.gate.mat g.wires =
            Matrix.diagonal (fun x : Qubits n =>
              if x (w 0) then Complex.exp ((θ : ℂ) * Complex.I) else 1) := by
          rw [embedOp_of_gate_eq hθ.2 g.wires w (fun _ => rfl)]
          exact embedOp_rot_eq_diagonal θ w
        have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
        have hnonneg : 0 ≤ (D : ℝ) * θ / (2 * Real.pi) :=
          div_nonneg (mul_nonneg hDpos.le hθ.1.1.le) hpi.le
        have hj_lt_D : j < D := by
          rw [Nat.floor_lt hnonneg, div_lt_iff₀ hpi, mul_comm (D : ℝ) θ, mul_comm (D : ℝ) (2 * Real.pi)]
          exact mul_lt_mul_of_pos_right hθ.1.2 hDpos
        have hg'_op : embedOp (roundGateApp D hD g).gate.mat (roundGateApp D hD g).wires =
            Matrix.diagonal (fun x : Qubits n =>
              if x (w 0) then Complex.exp ((φ : ℂ) * Complex.I) else 1) := by
          have hround : roundGateApp D hD g =
              ⟨Gate.ofMatrix1 (rot φ), Or.inr ⟨j, hj_lt_D, rfl⟩, w⟩ := by
            dsimp only [roundGateApp]
            rw [dif_neg h1]
          rw [hround]
          exact embedOp_rot_eq_diagonal φ w
        let d' : Fin m × Qubits n → ℂ := fun p =>
          if p.2 (w 0) then Complex.exp ((φ : ℂ) * Complex.I) else 1
        let d : Fin m × Qubits n → ℂ := fun p =>
          if p.2 (w 0) then Complex.exp ((θ : ℂ) * Complex.I) else 1
        have hUm' : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ
            embedOp (roundGateApp D hD g).gate.mat (roundGateApp D hD g).wires =
            Matrix.diagonal d' := by
          rw [hg'_op, kronecker_one_diagonal]
        have hUm : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ embedOp g.gate.mat g.wires =
            Matrix.diagonal d := by
          rw [hg_op, kronecker_one_diagonal]
        rw [hUm', hUm]
        have hd'_norm : ∀ p, ‖d' p‖ = 1 := by
          intro p
          dsimp only [d']
          split_ifs
          · exact Complex.norm_exp_ofReal_mul_I φ
          · exact norm_one
        have hd_norm : ∀ p, ‖d p‖ = 1 := by
          intro p
          dsimp only [d]
          split_ifs
          · exact Complex.norm_exp_ofReal_mul_I θ
          · exact norm_one
        have hdiag_unitary : Matrix.diagonal d' ∈ Matrix.unitaryGroup (Fin m × Qubits n) ℂ := by
          rw [Matrix.mem_unitaryGroup_iff]
          change Matrix.diagonal d' * (Matrix.diagonal d')ᴴ = 1
          have hstar : (Matrix.diagonal d')ᴴ = Matrix.diagonal (fun x => star (d' x)) := by
            ext x y
            simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
            by_cases h : x = y
            · subst h; simp
            · rw [if_neg (Ne.symm h), if_neg h, star_zero]
          rw [hstar, Matrix.diagonal_mul_diagonal]
          ext p q
          simp only [Matrix.diagonal_apply, Matrix.one_apply]
          by_cases h : p = q
          · subst h
            simp only [↓reduceIte, Complex.star_def]
            rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
              hd'_norm p, one_pow, Complex.ofReal_one]
          · simp [h]
        have hρ' := s1.isDensityOperator_conj_unitary hρ hdiag_unitary
        have hHerm1 : ((roundCircuit D hD k).channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ)).IsHermitian :=
          channelRef_isHermitian _ m hρ'.1.isHermitian
        have hHerm2 : (k.channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ)).IsHermitian :=
          channelRef_isHermitian k m hρ'.1.isHermitian
        have hHerm3 : (k.channelRef m (Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ)).IsHermitian :=
          channelRef_isHermitian k m (isHermitian_conj hρ.1.isHermitian _)
        have htri := s1.traceDist_triangle hHerm1 hHerm2 hHerm3
        have hpart1 : WildeQIT.traceDist
            ((roundCircuit D hD k).channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ))
            (k.channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ)) ≤
            4 * Real.pi * (k.maxGates : ℝ) / (D : ℝ) :=
          ih m _ hρ'
        have hj_le : (j : ℝ) ≤ (D : ℝ) * θ / (2 * Real.pi) := Nat.floor_le hnonneg
        have hj_lt : (D : ℝ) * θ / (2 * Real.pi) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
        have hφ_le_θ : φ ≤ θ := by
          dsimp only [φ]
          rw [div_le_iff₀ hDpos]
          have := (le_div_iff₀ hpi).mp hj_le
          linarith
        have hθ_lt_φ : θ < φ + 2 * Real.pi / (D : ℝ) := by
          dsimp only [φ]
          have h1' : (D : ℝ) * θ < ((j : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ hpi).mp hj_lt
          have h2' : θ < ((j : ℝ) + 1) * (2 * Real.pi) / (D : ℝ) := (lt_div_iff₀' hDpos).mpr h1'
          linarith [show ((j : ℝ) + 1) * (2 * Real.pi) / (D : ℝ) =
            2 * Real.pi * (j : ℝ) / (D : ℝ) + 2 * Real.pi / (D : ℝ) by ring]
        have hδ_nonneg : 0 ≤ 2 * Real.pi / (D : ℝ) := by positivity
        have hdiff_le : ∀ p, ‖d' p - d p‖ ≤ 2 * Real.pi / (D : ℝ) := by
          intro p
          dsimp only [d', d]
          split_ifs
          · calc ‖Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)‖
                ≤ |φ - θ| := norm_exp_ofReal_mul_I_sub_exp_ofReal_mul_I_le φ θ
              _ = θ - φ := by rw [abs_of_nonpos (sub_nonpos.mpr hφ_le_θ)]; ring
              _ ≤ 2 * Real.pi / (D : ℝ) := by linarith
          · simp [hδ_nonneg]
        have hpart2 : WildeQIT.traceDist
            (k.channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ))
            (k.channelRef m (Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ)) ≤
            4 * Real.pi / (D : ℝ) := by
          rw [WildeQIT.traceDist, channelRef_sub]
          have hX_herm : (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ -
              Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ).IsHermitian :=
            hρ'.1.isHermitian.sub (isHermitian_conj hρ.1.isHermitian _)
          have hcptp : WildeQIT.traceNorm
              (k.channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ -
                Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ)) ≤
              WildeQIT.traceNorm
                (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ -
                  Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ) := by
            dsimp only [AdaptiveCircuit.channelRef]
            have hmap : (k.krausList.map fun K =>
                ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) *
                  (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ -
                    Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ) *
                  ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ) =
                ((k.krausList.map fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K).map
                  fun K => K *
                    (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ -
                      Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ) * Kᴴ) := by
              rw [List.map_map]
              rfl
            rw [hmap]
            exact s1.cptp_traceNorm_le
              (k.krausList.map fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)
              (channelRef_kraus_sum_one hcnotRotGates_isUnitary k m) hX_herm
          have hdiag_dist : WildeQIT.traceDist
              (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ)
              (Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ) ≤
              2 * (2 * Real.pi / (D : ℝ)) :=
            s1.traceDist_conj_diag_unitary_le d' d hd'_norm hd_norm hδ_nonneg hdiff_le hρ
          calc WildeQIT.traceNorm
                (k.channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ -
                  Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ))
              ≤ WildeQIT.traceNorm
                  (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ -
                    Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ) := hcptp
            _ = WildeQIT.traceDist
                  (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ)
                  (Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ) := rfl
            _ ≤ 2 * (2 * Real.pi / (D : ℝ)) := hdiag_dist
            _ = 4 * Real.pi / (D : ℝ) := by ring
        calc WildeQIT.traceDist
              ((roundCircuit D hD k).channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ))
              (k.channelRef m (Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ))
            ≤ WildeQIT.traceDist
                ((roundCircuit D hD k).channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ))
                (k.channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ)) +
              WildeQIT.traceDist
                (k.channelRef m (Matrix.diagonal d' * ρ * (Matrix.diagonal d')ᴴ))
                (k.channelRef m (Matrix.diagonal d * ρ * (Matrix.diagonal d)ᴴ)) := htri
          _ ≤ 4 * Real.pi * (k.maxGates : ℝ) / (D : ℝ) + 4 * Real.pi / (D : ℝ) :=
              add_le_add hpart1 hpart2
          _ = 4 * Real.pi * ((1 + k.maxGates : ℕ) : ℝ) / (D : ℝ) := by
              push_cast
              ring
  | measure q k ih =>
      intro m ρ hρ
      simp only [roundCircuit, AdaptiveCircuit.maxGates]
      rw [channelRef_measure, channelRef_measure]
      rcases s1.proj_decomp_density q hρ with
        ⟨pf, pt, ρf, ρt, hpf0, hpt0, hpft, hρf, hρt, hdecf, hdect⟩
      rw [hdecf, hdect, channelRef_smul, channelRef_smul, channelRef_smul, channelRef_smul]
      have hsub :
          ((pf : ℂ) • (roundCircuit D hD (k false)).channelRef m ρf +
            (pt : ℂ) • (roundCircuit D hD (k true)).channelRef m ρt) -
          ((pf : ℂ) • (k false).channelRef m ρf +
            (pt : ℂ) • (k true).channelRef m ρt) =
          (pf : ℂ) • ((roundCircuit D hD (k false)).channelRef m ρf - (k false).channelRef m ρf) +
          (pt : ℂ) • ((roundCircuit D hD (k true)).channelRef m ρt - (k true).channelRef m ρt) := by
        simp only [smul_sub]
        abel
      have hHf : ((roundCircuit D hD (k false)).channelRef m ρf - (k false).channelRef m ρf).IsHermitian :=
        (channelRef_isHermitian _ m hρf.1.isHermitian).sub (channelRef_isHermitian _ m hρf.1.isHermitian)
      have hHt : ((roundCircuit D hD (k true)).channelRef m ρt - (k true).channelRef m ρt).IsHermitian :=
        (channelRef_isHermitian _ m hρt.1.isHermitian).sub (channelRef_isHermitian _ m hρt.1.isHermitian)
      rw [WildeQIT.traceDist, hsub]
      have hadd := s1.traceNorm_add_le (isHermitian_real_smul pf hHf) (isHermitian_real_smul pt hHt)
      rw [s1.traceNorm_smul_of_nonneg hpf0 hHf, s1.traceNorm_smul_of_nonneg hpt0 hHt] at hadd
      have ihf : WildeQIT.traceNorm
          ((roundCircuit D hD (k false)).channelRef m ρf - (k false).channelRef m ρf) ≤
          4 * Real.pi * ((k false).maxGates : ℝ) / (D : ℝ) := ih false m ρf hρf
      have iht : WildeQIT.traceNorm
          ((roundCircuit D hD (k true)).channelRef m ρt - (k true).channelRef m ρt) ≤
          4 * Real.pi * ((k true).maxGates : ℝ) / (D : ℝ) := ih true m ρt hρt
      have hm1 : 4 * Real.pi * ((k false).maxGates : ℝ) / (D : ℝ) ≤
          4 * Real.pi * ((max (k false).maxGates (k true).maxGates : ℕ) : ℝ) / (D : ℝ) := by
        apply div_le_div_of_nonneg_right _ hDpos.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast le_max_left (k false).maxGates (k true).maxGates
      have hm2 : 4 * Real.pi * ((k true).maxGates : ℝ) / (D : ℝ) ≤
          4 * Real.pi * ((max (k false).maxGates (k true).maxGates : ℕ) : ℝ) / (D : ℝ) := by
        apply div_le_div_of_nonneg_right _ hDpos.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast le_max_right (k false).maxGates (k true).maxGates
      calc WildeQIT.traceNorm
            ((pf : ℂ) • ((roundCircuit D hD (k false)).channelRef m ρf - (k false).channelRef m ρf) +
              (pt : ℂ) • ((roundCircuit D hD (k true)).channelRef m ρt - (k true).channelRef m ρt))
          ≤ pf * WildeQIT.traceNorm
              ((roundCircuit D hD (k false)).channelRef m ρf - (k false).channelRef m ρf) +
            pt * WildeQIT.traceNorm
              ((roundCircuit D hD (k true)).channelRef m ρt - (k true).channelRef m ρt) := hadd
        _ ≤ pf * (4 * Real.pi * ((max (k false).maxGates (k true).maxGates : ℕ) : ℝ) / (D : ℝ)) +
            pt * (4 * Real.pi * ((max (k false).maxGates (k true).maxGates : ℕ) : ℝ) / (D : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_trans ihf hm1) hpf0)
              (mul_le_mul_of_nonneg_left (le_trans iht hm2) hpt0)
        _ = (pf + pt) * (4 * Real.pi * ((max (k false).maxGates (k true).maxGates : ℕ) : ℝ) / (D : ℝ)) := by
            ring
        _ = 4 * Real.pi * ((max (k false).maxGates (k true).maxGates : ℕ) : ℝ) / (D : ℝ) := by
            rw [hpft, one_mul]

end Step2Helpers

theorem step2_compile_to_grid (s1 : Step1API) (N : ℕ)
    (hDecomp : ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (QAlgorithms.Qubits k) (QAlgorithms.Qubits k) ℂ,
        U ∈ Matrix.unitaryGroup (QAlgorithms.Qubits k) ℂ →
        ∃ c : QAlgorithms.Circuit ConstOverheadCompile.Main.HCnotRotGates k,
          c.size ≤ N ∧ c.unitary = U)
    (D : ℕ) (hD : 1 ≤ D) (n G : ℕ)
    (A : ConstOverheadCompile.Main.AdaptiveCircuit ConstOverheadCompile.Main.ArbGates n)
    (hG : A.maxGates ≤ G) :
    ∃ A₂ : ConstOverheadCompile.Main.AdaptiveCircuit
        (ConstOverheadCompile.Main.CliffordT ∪ ConstOverheadCompile.Main.gridGates D) n,
      A₂.maxGates ≤ N * G ∧
      ConstOverheadCompile.Main.DiamondClose A₂.channelRef A.channelRef
        (4 * Real.pi * ((N * G : ℕ) : ℝ) / (D : ℝ)) := by
  let A₁ := expandCircuit N hDecomp A
  let A₂ := roundCircuit D hD A₁
  refine ⟨A₂, ?_, ?_⟩
  · rw [roundCircuit_maxGates]
    exact le_trans (expandCircuit_maxGates N hDecomp A) (Nat.mul_le_mul_left N hG)
  · intro m ρ hρ
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hD
    have hch : A₁.channelRef m ρ = A.channelRef m ρ := by
      dsimp only [A₁, ConstOverheadCompile.Main.AdaptiveCircuit.channelRef]
      rw [expandCircuit_krausList N hDecomp A]
    rw [← hch]
    refine le_trans (roundCircuit_channelRef_close s1 D hD A₁ m ρ hρ) ?_
    apply div_le_div_of_nonneg_right _ hDpos.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast le_trans (expandCircuit_maxGates N hDecomp A) (Nat.mul_le_mul_left N hG)

theorem step2_diamondClose_trans (s1 : Step1API)
    {S₁ S₂ S₃ : Set QAlgorithms.Gate} {n a : ℕ}
    (A' : ConstOverheadCompile.Main.AdaptiveCircuit S₁ (n + a))
    (A₂ : ConstOverheadCompile.Main.AdaptiveCircuit S₂ n)
    (A : ConstOverheadCompile.Main.AdaptiveCircuit S₃ n)
    {ε₁ ε₂ ε : ℝ}
    (h1 : ConstOverheadCompile.Main.DiamondClose A'.dataChannelRef A₂.channelRef ε₁)
    (h2 : ConstOverheadCompile.Main.DiamondClose A₂.channelRef A.channelRef ε₂)
    (hε : ε₁ + ε₂ ≤ ε) :
    ConstOverheadCompile.Main.DiamondClose A'.dataChannelRef A.channelRef ε := by
  intro m ρ hρ
  have hH : ρ.IsHermitian := hρ.1.1
  calc WildeQIT.traceDist (A'.dataChannelRef m ρ) (A.channelRef m ρ)
      ≤ WildeQIT.traceDist (A'.dataChannelRef m ρ) (A₂.channelRef m ρ) +
          WildeQIT.traceDist (A₂.channelRef m ρ) (A.channelRef m ρ) :=
        s1.traceDist_triangle (dataChannelRef_isHermitian A' m hH)
          (channelRef_isHermitian A₂ m hH) (channelRef_isHermitian A m hH)
    _ ≤ ε₁ + ε₂ := add_le_add (h1 m ρ hρ) (h2 m ρ hρ)
    _ ≤ ε := hε

private lemma step3_log_le_self {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  linarith [Real.log_le_sub_one_of_pos hx]

private lemma step3_log_le_two_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * x ^ ((1 : ℝ) / 2) := by
  have h1 : Real.log (x ^ ((1 : ℝ) / 2)) ≤ x ^ ((1 : ℝ) / 2) :=
    step3_log_le_self (Real.rpow_pos_of_pos hx _)
  rw [Real.log_rpow hx] at h1
  linarith

theorem step3_choose_params :
    ∀ (N : ℕ) (C₀ K c : ℝ), 0 < K → 0 < c →
      ∃ C : ℝ, ∀ G : ℕ, 1 ≤ G →
        ∃ (r b : ℕ) (ε₉ : ℝ),
          2 ≤ r ∧ 0 < ε₉ ∧ ε₉ ≤ 1 ∧ 1 ≤ (2 ^ b) ^ r ∧
          ε₉ + 4 * Real.pi * ((N * G : ℕ) : ℝ) / (((2 ^ b) ^ r : ℕ) : ℝ) ≤
            1 / (K * (G : ℝ) ^ c) ∧
          C₀ * ((r : ℝ) * ((N * G : ℕ) : ℝ) +
            (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) *
              Real.log (ε₉⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b))) ≤
            C * (G : ℝ) := by
  intro N C₀ K c hK hc
  let r : ℕ := 8 * (Nat.ceil (1 + c) + 1)
  let M : ℝ := 8 * Real.pi * (N : ℝ) * K + 2
  let A : ℝ := 4 * M
  let B : ℝ := (2 + 2 * K) * A ^ 2 * (r : ℝ)
  let C₁ : ℝ := (r : ℝ) * (N : ℝ) + (r : ℝ) * A ^ 2 * (B + 2 * (c + 1))
  refine ⟨max C₀ 0 * C₁, ?_⟩
  intro G hG
  have hG1 : (1 : ℝ) ≤ (G : ℝ) := by exact_mod_cast hG
  have hGpos : (0 : ℝ) < (G : ℝ) := lt_of_lt_of_le zero_lt_one hG1
  have hGc1 : (1 : ℝ) ≤ (G : ℝ) ^ c := Real.one_le_rpow hG1 hc.le
  have hGc_pos : (0 : ℝ) < (G : ℝ) ^ c := Real.rpow_pos_of_pos hGpos c
  have hG18_1 : (1 : ℝ) ≤ (G : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hG1 (by norm_num)
  have hG12_1 : (1 : ℝ) ≤ (G : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hG1 (by norm_num)
  have hM2 : 2 ≤ M := by
    have hpiK : 0 ≤ 8 * Real.pi * (N : ℝ) * K := by positivity
    dsimp only [M]
    linarith
  have hApos : 0 < A := by dsimp only [A]; linarith
  have hr8 : 8 ≤ r := by dsimp only [r]; omega
  have hr2 : 2 ≤ r := by omega
  have hB_pos : 0 < B := by
    have hr_r : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    dsimp only [B]
    positivity
  have hr_ge : (1 : ℝ) + c ≤ (r : ℝ) / 8 := by
    have hceil : (1 : ℝ) + c ≤ (Nat.ceil (1 + c) : ℝ) := Nat.le_ceil (1 + c)
    have hr_cast : (r : ℝ) = 8 * ((Nat.ceil (1 + c) : ℝ) + 1) := by
      dsimp only [r]
      push_cast
      ring
    linarith
  let T : ℝ := M * (G : ℝ) ^ ((1 : ℝ) / 8)
  have hT2 : 2 ≤ T := by
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ M * (G : ℝ) ^ ((1 : ℝ) / 8) := by gcongr
  let b : ℕ := Nat.log 2 (Nat.ceil T) + 1
  let ε₉ : ℝ := min (1 / 2) (1 / (2 * K * (G : ℝ) ^ c))
  have hT_le_pow : T ≤ (2 : ℝ) ^ b := by
    have hceil_lt : Nat.ceil T < 2 ^ b :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nat.ceil T)
    have h1 : T ≤ (Nat.ceil T : ℝ) := Nat.le_ceil T
    have h2 : ((Nat.ceil T : ℕ) : ℝ) < ((2 ^ b : ℕ) : ℝ) := Nat.cast_lt.mpr hceil_lt
    have h3 : ((2 ^ b : ℕ) : ℝ) = (2 : ℝ) ^ b := by push_cast; rfl
    linarith
  refine ⟨r, b, ε₉, hr2, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < ε₉
    have hpos2 : 0 < 1 / (2 * K * (G : ℝ) ^ c) := by positivity
    exact lt_min (by norm_num) hpos2
  · -- ε₉ ≤ 1
    have hle : ε₉ ≤ 1 / 2 := min_le_left _ _
    linarith
  · -- 1 ≤ (2 ^ b) ^ r
    exact Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by norm_num))
  · -- ε₉ + 4 * Real.pi * ((N * G : ℕ) : ℝ) / (((2 ^ b) ^ r : ℕ) : ℝ) ≤ 1 / (K * (G : ℝ) ^ c)
    have hε_bound : ε₉ ≤ 1 / (2 * K * (G : ℝ) ^ c) := min_le_right _ _
    have hpow_ge : M * ((G : ℝ) * (G : ℝ) ^ c) ≤ (((2 ^ b) ^ r : ℕ) : ℝ) := by
      have hpow_cast : (((2 ^ b) ^ r : ℕ) : ℝ) = ((2 : ℝ) ^ b) ^ r := by push_cast; rfl
      rw [hpow_cast]
      have hTr_le : T ^ r ≤ ((2 : ℝ) ^ b) ^ r := pow_le_pow_left₀ (by linarith) hT_le_pow r
      have hTr_eq : T ^ r = M ^ r * ((G : ℝ) ^ ((1 : ℝ) / 8)) ^ r := by
        dsimp only [T]
        rw [mul_pow]
      have hM_le_Mr : M ≤ M ^ r := le_self_pow₀ (by linarith) (by omega)
      have hG_pow : (G : ℝ) * (G : ℝ) ^ c ≤ ((G : ℝ) ^ ((1 : ℝ) / 8)) ^ r := by
        rw [← Real.rpow_natCast ((G : ℝ) ^ ((1 : ℝ) / 8)) r, ← Real.rpow_mul hGpos.le]
        have hexp : 1 + c ≤ (1 : ℝ) / 8 * (r : ℝ) := by linarith
        have hle_rpow : (G : ℝ) ^ (1 + c) ≤ (G : ℝ) ^ ((1 : ℝ) / 8 * (r : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hG1 hexp
        have hadd : (G : ℝ) ^ (1 + c) = (G : ℝ) * (G : ℝ) ^ c := by
          rw [Real.rpow_add hGpos, Real.rpow_one]
        linarith
      have hG_prod_nonneg : 0 ≤ (G : ℝ) * (G : ℝ) ^ c := by positivity
      calc
        M * ((G : ℝ) * (G : ℝ) ^ c) ≤ M ^ r * ((G : ℝ) ^ ((1 : ℝ) / 8)) ^ r :=
          mul_le_mul hM_le_Mr hG_pow hG_prod_nonneg (by positivity)
        _ = T ^ r := hTr_eq.symm
        _ ≤ ((2 : ℝ) ^ b) ^ r := hTr_le
    have hdenom_pos : (0 : ℝ) < (((2 ^ b) ^ r : ℕ) : ℝ) := by positivity
    have h2K_pos : 0 < 2 * K * (G : ℝ) ^ c := by positivity
    have herr2 : 4 * Real.pi * ((N * G : ℕ) : ℝ) / (((2 ^ b) ^ r : ℕ) : ℝ) ≤
        1 / (2 * K * (G : ℝ) ^ c) := by
      rw [div_le_div_iff₀ hdenom_pos h2K_pos]
      have hNG : ((N * G : ℕ) : ℝ) = (N : ℝ) * (G : ℝ) := by push_cast; rfl
      rw [hNG]
      have hM_ge : 8 * Real.pi * (N : ℝ) * K ≤ M := by
        dsimp only [M]
        linarith
      have hG_prod_nonneg : 0 ≤ (G : ℝ) * (G : ℝ) ^ c := by positivity
      calc
        4 * Real.pi * ((N : ℝ) * (G : ℝ)) * (2 * K * (G : ℝ) ^ c)
            = (8 * Real.pi * (N : ℝ) * K) * ((G : ℝ) * (G : ℝ) ^ c) := by ring
        _ ≤ M * ((G : ℝ) * (G : ℝ) ^ c) :=
            mul_le_mul_of_nonneg_right hM_ge hG_prod_nonneg
        _ ≤ (((2 ^ b) ^ r : ℕ) : ℝ) := hpow_ge
        _ = 1 * (((2 ^ b) ^ r : ℕ) : ℝ) := (one_mul _).symm
    calc
      ε₉ + 4 * Real.pi * ((N * G : ℕ) : ℝ) / (((2 ^ b) ^ r : ℕ) : ℝ)
          ≤ 1 / (2 * K * (G : ℝ) ^ c) + 1 / (2 * K * (G : ℝ) ^ c) := add_le_add hε_bound herr2
      _ = 1 / (K * (G : ℝ) ^ c) := by ring
  · -- Gate overhead bound
    have h2b_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ b := le_trans hT2 hT_le_pow
    have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
    have h2b_le : (2 : ℝ) ^ b ≤ A * (G : ℝ) ^ ((1 : ℝ) / 8) := by
      have hceil_ne : Nat.ceil T ≠ 0 := by
        have hceil_pos : 0 < Nat.ceil T := Nat.ceil_pos.mpr (by linarith)
        omega
      have hpow_le : 2 ^ Nat.log 2 (Nat.ceil T) ≤ Nat.ceil T :=
        Nat.pow_log_le_self 2 hceil_ne
      have hpow_le_r : ((2 ^ Nat.log 2 (Nat.ceil T) : ℕ) : ℝ) ≤ (Nat.ceil T : ℝ) := by
        exact_mod_cast hpow_le
      have hceil_ub : (Nat.ceil T : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      have hb_eq : (2 : ℝ) ^ b = 2 * ((2 ^ Nat.log 2 (Nat.ceil T) : ℕ) : ℝ) := by
        dsimp only [b]
        rw [pow_succ']
        push_cast
        rfl
      have hT_eq : 4 * T = A * (G : ℝ) ^ ((1 : ℝ) / 8) := by
        dsimp only [A, T]
        ring
      linarith
    have hL1_gt : (1 : ℝ) / 2 < Real.log ((2 : ℝ) ^ b) := by
      have hlog2 : Real.log 2 ≤ Real.log ((2 : ℝ) ^ b) :=
        Real.log_le_log (by norm_num) h2b_ge2
      linarith [Real.log_two_gt_d9]
    have hL1_pos : 0 < Real.log ((2 : ℝ) ^ b) := by linarith
    have hL1_le : Real.log ((2 : ℝ) ^ b) ≤ (2 : ℝ) ^ b := step3_log_le_self h2b_pos
    have hε_inv_ge2 : 2 ≤ ε₉⁻¹ := by
      rcases le_total ((1 : ℝ) / 2) (1 / (2 * K * (G : ℝ) ^ c)) with hle | hle
      · have hε_eq : ε₉ = 1 / 2 := min_eq_left hle
        rw [hε_eq]
        norm_num
      · have hε_eq : ε₉ = 1 / (2 * K * (G : ℝ) ^ c) := min_eq_right hle
        rw [hε_eq, one_div, inv_inv]
        have hle' : (2 * K * (G : ℝ) ^ c)⁻¹ ≤ 2⁻¹ := by simpa only [one_div] using hle
        exact (inv_le_inv₀ (by positivity) (by norm_num)).mp hle'
    have hε_inv_le : ε₉⁻¹ ≤ (2 + 2 * K) * (G : ℝ) ^ c := by
      rcases le_total ((1 : ℝ) / 2) (1 / (2 * K * (G : ℝ) ^ c)) with hle | hle
      · have hε_eq : ε₉ = 1 / 2 := min_eq_left hle
        rw [hε_eq]
        norm_num
        calc
          (2 : ℝ) = 2 * 1 := by ring
          _ ≤ (2 + 2 * K) * (G : ℝ) ^ c := by gcongr; linarith
      · have hε_eq : ε₉ = 1 / (2 * K * (G : ℝ) ^ c) := min_eq_right hle
        rw [hε_eq, one_div, inv_inv]
        have hle2K : 2 * K ≤ 2 + 2 * K := by linarith
        exact mul_le_mul_of_nonneg_right hle2K hGc_pos.le
    let X : ℝ := ε₉⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b)
    have hX_gt1 : 1 < X := by
      have hr_r : (8 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr8
      have hX_ge : (16 : ℝ) ≤ X := by
        dsimp only [X]
        calc
          (16 : ℝ) = 2 * 2 * 8 * (1 / 2) := by norm_num
          _ ≤ ε₉⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b) := by gcongr
      linarith
    have hX_pos : 0 < X := lt_trans zero_lt_one hX_gt1
    have hL2_pos : 0 < Real.log X := Real.log_pos hX_gt1
    have h2bL1_bound : (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) ≤ A ^ 2 * (G : ℝ) ^ ((1 : ℝ) / 4) := by
      have h1 : (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ b :=
        mul_le_mul_of_nonneg_left hL1_le h2b_pos.le
      have h2 : (2 : ℝ) ^ b * (2 : ℝ) ^ b ≤
          (A * (G : ℝ) ^ ((1 : ℝ) / 8)) * (A * (G : ℝ) ^ ((1 : ℝ) / 8)) :=
        mul_le_mul h2b_le h2b_le h2b_pos.le (by positivity)
      have h3 : (G : ℝ) ^ ((1 : ℝ) / 8) * (G : ℝ) ^ ((1 : ℝ) / 8) = (G : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hGpos]
        norm_num
      calc
        (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ b := h1
        _ ≤ (A * (G : ℝ) ^ ((1 : ℝ) / 8)) * (A * (G : ℝ) ^ ((1 : ℝ) / 8)) := h2
        _ = A ^ 2 * ((G : ℝ) ^ ((1 : ℝ) / 8) * (G : ℝ) ^ ((1 : ℝ) / 8)) := by ring
        _ = A ^ 2 * (G : ℝ) ^ ((1 : ℝ) / 4) := by rw [h3]
    have hX_le : X ≤ B * (G : ℝ) ^ (c + 1) := by
      have h1 : X ≤ ε₉⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * (2 : ℝ) ^ b := by
        dsimp only [X]
        gcongr
      have h2 : ε₉⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * (2 : ℝ) ^ b ≤
          ((2 + 2 * K) * (G : ℝ) ^ c) * (A * (G : ℝ) ^ ((1 : ℝ) / 8)) *
            (r : ℝ) * (A * (G : ℝ) ^ ((1 : ℝ) / 8)) := by
        have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        have hε_inv_nonneg : 0 ≤ ε₉⁻¹ := by linarith
        gcongr
      have hG14 : (G : ℝ) ^ ((1 : ℝ) / 8) * (G : ℝ) ^ ((1 : ℝ) / 8) = (G : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hGpos]
        norm_num
      have hGc_add : (G : ℝ) ^ c * (G : ℝ) ^ ((1 : ℝ) / 4) = (G : ℝ) ^ (c + 1 / 4) := by
        rw [← Real.rpow_add hGpos]
      have hGc_le : (G : ℝ) ^ (c + 1 / 4) ≤ (G : ℝ) ^ (c + 1) :=
        Real.rpow_le_rpow_of_exponent_le hG1 (by linarith)
      calc
        X ≤ ε₉⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * (2 : ℝ) ^ b := h1
        _ ≤ ((2 + 2 * K) * (G : ℝ) ^ c) * (A * (G : ℝ) ^ ((1 : ℝ) / 8)) *
              (r : ℝ) * (A * (G : ℝ) ^ ((1 : ℝ) / 8)) := h2
        _ = B * ((G : ℝ) ^ c * ((G : ℝ) ^ ((1 : ℝ) / 8) * (G : ℝ) ^ ((1 : ℝ) / 8))) := by
            dsimp only [B]; ring
        _ = B * (G : ℝ) ^ (c + 1 / 4) := by rw [hG14, hGc_add]
        _ ≤ B * (G : ℝ) ^ (c + 1) := mul_le_mul_of_nonneg_left hGc_le hB_pos.le
    have hL2_le : Real.log X ≤ (B + 2 * (c + 1)) * (G : ℝ) ^ ((1 : ℝ) / 2) := by
      have hlog_le : Real.log X ≤ Real.log (B * (G : ℝ) ^ (c + 1)) :=
        Real.log_le_log hX_pos hX_le
      have hlog_mul : Real.log (B * (G : ℝ) ^ (c + 1)) =
          Real.log B + (c + 1) * Real.log (G : ℝ) := by
        rw [Real.log_mul hB_pos.ne' (Real.rpow_pos_of_pos hGpos _).ne', Real.log_rpow hGpos]
      have hlogB : Real.log B ≤ B * (G : ℝ) ^ ((1 : ℝ) / 2) := by
        have h1 : Real.log B ≤ B := step3_log_le_self hB_pos
        calc
          Real.log B ≤ B := h1
          _ = B * 1 := by ring
          _ ≤ B * (G : ℝ) ^ ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hG12_1 hB_pos.le
      have hlogG : Real.log (G : ℝ) ≤ 2 * (G : ℝ) ^ ((1 : ℝ) / 2) :=
        step3_log_le_two_sqrt hGpos
      have hc1_nonneg : 0 ≤ c + 1 := by linarith
      calc
        Real.log X ≤ Real.log (B * (G : ℝ) ^ (c + 1)) := hlog_le
        _ = Real.log B + (c + 1) * Real.log (G : ℝ) := hlog_mul
        _ ≤ B * (G : ℝ) ^ ((1 : ℝ) / 2) +
              (c + 1) * (2 * (G : ℝ) ^ ((1 : ℝ) / 2)) :=
            add_le_add hlogB (mul_le_mul_of_nonneg_left hlogG hc1_nonneg)
        _ = (B + 2 * (c + 1)) * (G : ℝ) ^ ((1 : ℝ) / 2) := by ring
    have hterm2_le : (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) * Real.log X ≤
        (r : ℝ) * A ^ 2 * (B + 2 * (c + 1)) * (G : ℝ) := by
      have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      have hprod : (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) * Real.log X ≤
          (A ^ 2 * (G : ℝ) ^ ((1 : ℝ) / 4)) *
            ((B + 2 * (c + 1)) * (G : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul h2bL1_bound hL2_le hL2_pos.le (by positivity)
      have hG34 : (G : ℝ) ^ ((1 : ℝ) / 4) * (G : ℝ) ^ ((1 : ℝ) / 2) = (G : ℝ) ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add hGpos]
        norm_num
      have hG34_le : (G : ℝ) ^ ((3 : ℝ) / 4) ≤ (G : ℝ) := by
        calc
          (G : ℝ) ^ ((3 : ℝ) / 4) ≤ (G : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hG1 (by norm_num)
          _ = (G : ℝ) := Real.rpow_one (G : ℝ)
      have hcoef_nonneg : 0 ≤ (r : ℝ) * A ^ 2 * (B + 2 * (c + 1)) := by positivity
      calc
        (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) * Real.log X
            = (r : ℝ) * ((2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) * Real.log X) := by ring
        _ ≤ (r : ℝ) * ((A ^ 2 * (G : ℝ) ^ ((1 : ℝ) / 4)) *
              ((B + 2 * (c + 1)) * (G : ℝ) ^ ((1 : ℝ) / 2))) :=
            mul_le_mul_of_nonneg_left hprod hr_nonneg
        _ = (r : ℝ) * A ^ 2 * (B + 2 * (c + 1)) *
              ((G : ℝ) ^ ((1 : ℝ) / 4) * (G : ℝ) ^ ((1 : ℝ) / 2)) := by ring
        _ = (r : ℝ) * A ^ 2 * (B + 2 * (c + 1)) * (G : ℝ) ^ ((3 : ℝ) / 4) := by rw [hG34]
        _ ≤ (r : ℝ) * A ^ 2 * (B + 2 * (c + 1)) * (G : ℝ) :=
            mul_le_mul_of_nonneg_left hG34_le hcoef_nonneg
    have hP_nonneg : 0 ≤ (r : ℝ) * ((N * G : ℕ) : ℝ) +
        (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) * Real.log X := by
      have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      have hNG_nonneg : (0 : ℝ) ≤ ((N * G : ℕ) : ℝ) := Nat.cast_nonneg _
      positivity
    have hP_le : (r : ℝ) * ((N * G : ℕ) : ℝ) +
        (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) * Real.log X ≤ C₁ * (G : ℝ) := by
      have hNG : ((N * G : ℕ) : ℝ) = (N : ℝ) * (G : ℝ) := by push_cast; rfl
      rw [hNG]
      dsimp only [C₁]
      linarith
    have hC₀_le : C₀ ≤ max C₀ 0 := le_max_left C₀ 0
    have hmax_nonneg : 0 ≤ max C₀ 0 := le_max_right C₀ 0
    calc
      C₀ * ((r : ℝ) * ((N * G : ℕ) : ℝ) +
          (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) * Real.log X)
          ≤ max C₀ 0 * ((r : ℝ) * ((N * G : ℕ) : ℝ) +
              (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) * Real.log X) :=
            mul_le_mul_of_nonneg_right hC₀_le hP_nonneg
      _ ≤ max C₀ 0 * (C₁ * (G : ℝ)) := mul_le_mul_of_nonneg_left hP_le hmax_nonneg
      _ = max C₀ 0 * C₁ * (G : ℝ) := by ring

theorem solution :
    ∀ K c : ℝ, 0 < K → 0 < c → ∃ C : ℝ, ∀ (n G : ℕ), 1 ≤ G →
      ∀ A : ConstOverheadCompile.Main.AdaptiveCircuit ConstOverheadCompile.Main.ArbGates n,
        A.maxGates ≤ G →
        ∃ (a : ℕ) (A' : ConstOverheadCompile.Main.AdaptiveCircuit ConstOverheadCompile.Main.CliffordT (n + a)),
          (A'.maxGates : ℝ) ≤ C * G ∧
          ConstOverheadCompile.Main.DiamondClose A'.dataChannelRef A.channelRef
            (1 / (K * (G : ℝ) ^ c)) := by
  let s1 : Step1API :=
    { traceDist_self := step1_traceDist_self
      traceNorm_add_le := step1_traceNorm_add_le
      traceDist_triangle := step1_traceDist_triangle
      traceNorm_smul_of_nonneg := step1_traceNorm_smul_of_nonneg
      isDensityOperator_conj_unitary := step1_isDensityOperator_conj_unitary
      cptp_traceNorm_le := step1_cptp_traceNorm_le
      traceDist_conj_diag_unitary_le := step1_traceDist_conj_diag_unitary_le
      proj_decomp_density := step1_proj_decomp_density }
  obtain ⟨N, hDecomp⟩ := ConstOverheadCompile.Main.decomposition_cnot_h_rotation
  obtain ⟨C₀, hThm9⟩ := ConstOverheadCompile.Main.theorem_9
  intro K c hK hc
  obtain ⟨C, hParams⟩ := step3_choose_params N C₀ K c hK hc
  refine ⟨C, ?_⟩
  intro n G hG A hA_max
  obtain ⟨r, b, ε₉, hr2, hε₉_pos, hε₉_le1, hD_pos, hErr, hGate⟩ := hParams G hG
  obtain ⟨A₂, hA₂_max, hA₂_close⟩ :=
    step2_compile_to_grid s1 N hDecomp ((2 ^ b) ^ r) hD_pos n G A hA_max
  obtain ⟨a, A', hA'_max, hA'_close⟩ :=
    hThm9 r b hr2 ε₉ hε₉_pos hε₉_le1 n (N * G) A₂ hA₂_max
  exact ⟨a, A', le_trans hA'_max hGate,
    step2_diamondClose_trans s1 A' A₂ A hA'_close hA₂_close hErr⟩
