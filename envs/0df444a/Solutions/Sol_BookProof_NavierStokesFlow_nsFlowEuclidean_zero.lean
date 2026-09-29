-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsFlowEuclidean_zero
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:37:26.980078+00:00
-- url     : https://prove2.me/submissions/5e0321cc-84af-4525-943a-e766a3c3cba4

import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesCauchy
open scoped Matrix Matrix.Norms.Operator
namespace BookProof.NavierStokesFlow
open BookProof.ChapterContinuityUnitaryInfinite
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {n : ℕ} (d : NSTruncation n)


theorem symmetric_hasZeroDeficiency (H : F →ₗ[ℂ] F) (hsym : H.IsSymmetric) :
    HasZeroDeficiency H := by
  constructor
  · intro v hv
    have h := hsym v v
    rw [hv, inner_smul_left, inner_smul_right] at h
    have h2 : (2 * Complex.I) * (inner ℂ v v : ℂ) = 0 := by
      simp only [Complex.conj_I] at h
      linear_combination -h
    exact inner_self_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by simp [Complex.I_ne_zero]))
  · intro v hv
    have h := hsym v v
    rw [hv, inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right] at h
    have h2 : (2 * Complex.I) * (inner ℂ v v : ℂ) = 0 := by
      simp only [Complex.conj_I] at h
      linear_combination h
    exact inner_self_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by simp [Complex.I_ne_zero]))

theorem nsAdvection_hermitian (i : Fin 3) : (nsAdvection d i)ᴴ = nsAdvection d i := by
  simp only [nsAdvection, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, nsVelocity, nsGradVelocity,
    nsLapVelocity, d.u_herm, Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact Finset.sum_congr rfl fun j _ => d.u_comm _ _

theorem nsHamiltonian_hermitian : (nsHamiltonian d)ᴴ = nsHamiltonian d := by
  simp only [nsHamiltonian, Matrix.conjTranspose_sum, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, nsAdvection_hermitian, d.mom_herm]
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem nsFlow_unitary (t : ℝ) : (nsFlowUnitary d t)ᴴ * nsFlowUnitary d t = 1 :=
  BookProof.ChapterContinuityUnitary.exp_smul_I_unitary _ (nsHamiltonian_hermitian d) t

theorem nsFlow_zero : nsFlowUnitary d 0 = 1 := by
  simp [nsFlowUnitary, NormedSpace.exp_zero]

theorem nsFlow_norm_preserving (t : ℝ) (psi : Fin n → ℂ) :
    ∑ a, ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2 = ∑ a, ‖psi a‖ ^ 2 :=
  BookProof.ChapterContinuityUnitary.unitary_preserves_normSq _ (nsFlow_unitary d t) psi

@[simp] theorem applyVecCLM_apply (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    applyVecCLM x A = A *ᵥ x := rfl

theorem matrixFlow_hasDerivAt (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (matrixFlow A) (matrixFlow A t * A) t :=
  hasDerivAt_exp_smul_const (𝕂 := ℝ) A t

theorem matrixFlow_comm (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    matrixFlow A t * A = A * matrixFlow A t :=
  (((Commute.refl A).smul_left t).exp_left).eq

theorem matrixFlow_vec_hasDerivAt (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => matrixFlow A s *ᵥ x) (A *ᵥ (matrixFlow A t *ᵥ x)) t := by
  have h := (applyVecCLM x).hasFDerivAt.comp_hasDerivAt t (matrixFlow_hasDerivAt A t)
  convert h using 1 <;> first | rfl | (simp [applyVecCLM, matrixFlow_comm, Matrix.mulVec_mulVec, Function.comp_def] <;> rfl)

theorem nsFlowUnitary_eq_matrixFlow (t : ℝ) :
    nsFlowUnitary d t = matrixFlow (Complex.I • nsHamiltonian d) t := by
  rw [nsFlowUnitary, matrixFlow, ← smul_assoc, Complex.real_smul]

theorem nsFlowUnitary_eq_matrixFlow' :
    nsFlowUnitary d = matrixFlow (Complex.I • nsHamiltonian d) :=
  funext (nsFlowUnitary_eq_matrixFlow d)

theorem nsFlow_solves_schrodinger (psi : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => nsFlowUnitary d s *ᵥ psi)
      ((Complex.I • nsHamiltonian d) *ᵥ (nsFlowUnitary d t *ᵥ psi)) t := by
  rw [nsFlowUnitary_eq_matrixFlow']
  exact matrixFlow_vec_hasDerivAt (Complex.I • nsHamiltonian d) psi t

theorem eq_zero_of_inner_right_eq_zero_on_dense {D : Submodule ℂ F} (hdense : Dense (D : Set F))
    (w : F) (hw : ∀ v : D, (inner ℂ w (v : F) : ℂ) = 0) : w = 0 := by
  have hcont : Continuous fun y : F => (inner ℂ w y : ℂ) := (innerSL ℂ w).continuous
  have hall : (fun y : F => (inner ℂ w y : ℂ)) = fun _ => 0 :=
    Continuous.ext_on hdense hcont continuous_const fun x hx => hw ⟨x, hx⟩
  exact inner_self_eq_zero.mp (congrFun hall w)

theorem eq_zero_of_inner_left_eq_zero_on_dense {D : Submodule ℂ F} (hdense : Dense (D : Set F))
    (w : F) (hw : ∀ v : D, (inner ℂ (v : F) w : ℂ) = 0) : w = 0 :=
  eq_zero_of_inner_right_eq_zero_on_dense hdense w fun v => by
    rw [← inner_conj_symm, hw v, map_zero]

theorem eq_zero_of_hasDerivAt_smul_of_bounded (g : ℝ → ℂ) (s C : ℝ) (hs : s * s = 1)
    (hgd : ∀ t : ℝ, HasDerivAt g ((s : ℂ) * g t) t) (hb : ∀ t : ℝ, ‖g t‖ ≤ C) : g 0 = 0 := by
  set h : ℝ → ℂ := fun t => Real.exp (-(s * t)) • g t with hh
  have hhd : ∀ t : ℝ, HasDerivAt h 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(s * t))) (-s * Real.exp (-(s * t))) t := by
      have hlin : HasDerivAt (fun t : ℝ => -(s * t)) (-s) t := by
        convert hasDerivAt_const_mul (x := t) (-s) using 1 <;> first | rfl | (funext u; ring)
      simpa [mul_comm] using hlin.exp
    have h2 := h1.smul (hgd t)
    have heq : Real.exp (-(s * t)) • ((s : ℂ) * g t) + (-s * Real.exp (-(s * t))) • g t = 0 := by
      push_cast [Complex.real_smul]
      ring
    rw [heq] at h2
    exact h2
  have hconst : ∀ t : ℝ, h t = h 0 := fun t =>
    is_const_of_deriv_eq_zero (fun x => (hhd x).differentiableAt) (fun x => (hhd x).deriv) t 0
  have hb0 : ∀ T : ℝ, ‖g 0‖ ≤ Real.exp (-T) * C := by
    intro T
    have hst : s * (s * T) = T := by rw [← mul_assoc, hs, one_mul]
    have h3 := hconst (s * T)
    simp only [hh, hst, mul_zero, neg_zero, Real.exp_zero, one_smul] at h3
    rw [← h3, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le
  have htend : Filter.Tendsto (fun T : ℝ => Real.exp (-T) * C) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const C
  have hle : ‖g 0‖ ≤ 0 := ge_of_tendsto htend (Filter.Eventually.of_forall hb0)
  simpa using le_antisymm hle (norm_nonneg _)

theorem eq_zero_of_deficiency_of_completeUnitaryFlow (D : Submodule ℂ F) (H : D →ₗ[ℂ] D)
    (U : ℝ → F → F) (hdense : Dense (D : Set F)) (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖)
    (hU0 : ∀ v : F, U 0 v = v) (hUD : ∀ (t : ℝ) (v : D), U t (v : F) ∈ D)
    (hderiv : ∀ (v : D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F)) (Complex.I • (H ⟨U t (v : F), hUD t v⟩ : F)) t)
    (s : ℝ) (hs : s * s = 1) (w : F)
    (hw : ∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (((s : ℂ) * Complex.I) • w)) :
    w = 0 := by
  refine eq_zero_of_inner_right_eq_zero_on_dense hdense w fun v => ?_
  set g : ℝ → ℂ := fun t => inner ℂ w (U t (v : F)) with hg
  have hgd : ∀ t : ℝ, HasDerivAt g ((s : ℂ) * g t) t := by
    intro t
    have h1 : HasDerivAt g (inner ℂ w (Complex.I • (H ⟨U t (v : F), hUD t v⟩ : F)) : ℂ) t :=
      ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hderiv v t)
    have h2 : (inner ℂ w (Complex.I • (H ⟨U t (v : F), hUD t v⟩ : F)) : ℂ) = (s : ℂ) * g t := by
      have hk := hw ⟨U t (v : F), hUD t v⟩
      have hc : (inner ℂ w (H ⟨U t (v : F), hUD t v⟩ : F) : ℂ)
          = starRingEnd ℂ (inner ℂ (H ⟨U t (v : F), hUD t v⟩ : F) w) := (inner_conj_symm _ _).symm
      rw [hk, inner_smul_right] at hc
      rw [inner_smul_right, hc]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, inner_conj_symm, hg]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h2] at h1
    exact h1
  have hb : ∀ t : ℝ, ‖g t‖ ≤ ‖w‖ * ‖(v : F)‖ := fun t =>
    calc ‖g t‖ ≤ ‖w‖ * ‖U t (v : F)‖ := norm_inner_le_norm _ _
      _ = ‖w‖ * ‖(v : F)‖ := by rw [hnorm]
  simpa [hg, hU0] using eq_zero_of_hasDerivAt_smul_of_bounded g s (‖w‖ * ‖(v : F)‖) hs hgd hb

theorem hasZeroDeficiencyOn_of_completeUnitaryFlow (D : Submodule ℂ F) (H : D →ₗ[ℂ] D)
    (U : ℝ → F → F) (hdense : Dense (D : Set F)) (hnorm : ∀ (t : ℝ) (v : F), ‖U t v‖ = ‖v‖)
    (hU0 : ∀ v : F, U 0 v = v) (hUD : ∀ (t : ℝ) (v : D), U t (v : F) ∈ D)
    (hderiv : ∀ (v : D) (t : ℝ),
      HasDerivAt (fun s => U s (v : F)) (Complex.I • (H ⟨U t (v : F), hUD t v⟩ : F)) t) :
    HasZeroDeficiencyOn D H := by
  constructor
  · intro w hw
    refine eq_zero_of_deficiency_of_completeUnitaryFlow D H U hdense hnorm hU0 hUD hderiv 1
      (by norm_num) w fun v => ?_
    simpa using hw v
  · intro w hw
    refine eq_zero_of_deficiency_of_completeUnitaryFlow D H U hdense hnorm hU0 hUD hderiv (-1)
      (by norm_num) w fun v => ?_
    simpa using hw v

theorem hasZeroDeficiencyOn_of_bounded_symmetric (A : F →L[ℂ] F)
    (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (D : Submodule ℂ F) (hdense : Dense (D : Set F))
    (hinv : ∀ v : D, A (v : F) ∈ D) :
    HasZeroDeficiencyOn D
      (LinearMap.codRestrict D ((A : F →ₗ[ℂ] F).comp D.subtype) fun v => hinv v) := by
  have key : ∀ (c : ℂ) (w : F), (∀ v : D, (inner ℂ (A (v : F)) w : ℂ) = inner ℂ (v : F) (c • w)) →
      A w = c • w := by
    intro c w hw
    refine sub_eq_zero.mp (eq_zero_of_inner_left_eq_zero_on_dense hdense (A w - c • w) fun v => ?_)
    have hs := hsym (v : F) w
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [inner_sub_right, ← hw v, ← hs]
    ring
  constructor
  · intro w hw
    exact (symmetric_hasZeroDeficiency (A : F →ₗ[ℂ] F) hsym).1 w (key Complex.I w hw)
  · intro w hw
    refine (symmetric_hasZeroDeficiency (A : F →ₗ[ℂ] F) hsym).2 w ?_
    have := key (-Complex.I) w (fun v => by
      have hv := hw v
      change (inner ℂ (A (v : F)) w : ℂ) = inner ℂ (v : F) (-(Complex.I • w)) at hv
      simpa only [neg_smul] using hv)
    simpa using this

theorem single_mem_finiteModes (k : ℤ) (c : ℂ) : lp.single 2 k c ∈ finiteModes :=
  lpSingle_mem_lpFiniteModes k c

theorem continuityHamiltonian_mem_finiteModes (v : LinfZ) {f : L2Z} (hf : f ∈ finiteModes) :
    continuityHamiltonian v f ∈ finiteModes := by
  have hmom : ∀ {g : L2Z}, g ∈ finiteModes → momentum g ∈ finiteModes := by
    intro g hg
    have hstep := Submodule.smul_mem finiteModes (-Complex.I / 2)
      (Submodule.sub_mem finiteModes (shiftOp_mem_finiteModes 1 hg)
        (shiftOp_mem_finiteModes (-1) hg))
    simpa [momentum] using hstep
  have h1 : momentum (velocityOp v f) ∈ finiteModes := hmom (velocityOp_mem_finiteModes v hf)
  have h2 : velocityOp v (momentum f) ∈ finiteModes := velocityOp_mem_finiteModes v (hmom hf)
  have hstep := Submodule.smul_mem finiteModes (1 / 2 : ℂ) (Submodule.add_mem finiteModes h1 h2)
  simpa [continuityHamiltonian] using hstep

theorem nsFlowEuclidean_norm (t : ℝ) (psi : EuclideanSpace ℂ (Fin n)) :
    ‖nsFlowEuclidean d t psi‖ = ‖psi‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simpa [nsFlowEuclidean] using nsFlow_norm_preserving d t (WithLp.ofLp psi)

theorem nsFlowEuclidean_zero (psi : EuclideanSpace ℂ (Fin n)) :
    nsFlowEuclidean d 0 psi = psi := by
  simp [nsFlowEuclidean, nsFlow_zero]

theorem nsFlowEuclidean_hasDerivAt (psi : EuclideanSpace ℂ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => nsFlowEuclidean d s psi)
      (Complex.I • Matrix.toEuclideanLin (nsHamiltonian d) (nsFlowEuclidean d t psi)) t := by
  have h := nsFlow_solves_schrodinger d (WithLp.ofLp psi) t
  have h2 := ((((PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap).restrictScalars
      ℝ).hasFDerivAt).comp_hasDerivAt t h
  have heq : Complex.I • Matrix.toEuclideanLin (nsHamiltonian d) (nsFlowEuclidean d t psi)
      = WithLp.toLp 2
        ((Complex.I • nsHamiltonian d) *ᵥ (nsFlowUnitary d t *ᵥ WithLp.ofLp psi)) := by
    ext i
    simp [nsFlowEuclidean, Matrix.smul_mulVec]
  rw [heq]
  simpa [Function.comp_def, nsFlowEuclidean] using h2

theorem nsHamiltonian_hasZeroDeficiencyOn_of_flow :
    HasZeroDeficiencyOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
      (restrictToTop (Matrix.toEuclideanLin (nsHamiltonian d))) :=
  hasZeroDeficiencyOn_of_completeUnitaryFlow _ _ (nsFlowEuclidean d)
    (by simp) (fun t psi => nsFlowEuclidean_norm d t psi)
    (fun psi => nsFlowEuclidean_zero d psi) (fun _ _ => trivial)
    (fun psi t => nsFlowEuclidean_hasDerivAt d (psi : EuclideanSpace ℂ (Fin n)) t)

end BookProof.NavierStokesFlow

open BookProof.NavierStokesFlow

open scoped Matrix

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {ι : Type*}

open BookProof.ChapterContinuityUnitaryInfinite

variable {n : ℕ} (d : NSTruncation n)

theorem solution (psi : EuclideanSpace ℂ (Fin n)) :
    nsFlowEuclidean d 0 psi = psi := by
  exact BookProof.NavierStokesFlow.nsFlowEuclidean_zero d psi

#print axioms solution
