-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_convex_body_low_energy_tail
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T17:49:29.418984+00:00
-- url     : https://prove2.me/submissions/36dbd3dd-f6f1-4124-a8e3-75e33470c294

import Definitions.Def_BirkhoffGlobalSection_EHConvexPerturbation
import Theorems.Thm_BirkhoffGlobalSection_convex_body_of_star_shaped_level_set
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Homeomorph.Lemmas

/-! Very negative energy: rescale positions by `s = 1/√c`. The rescaled EH Hamiltonian
`Grs μ s` and its first two derivatives are jointly continuous through `s = 0`, where
the zero level is the ellipsoid `|y|²/2 + |X|²/4 = 1 - μ`. The tube lemma at
`(μ, s) = (1/2, 0)` gives the box barrier, strict star-shapedness and a positive
tangential Hessian. The convex body follows from `convex_body_of_star_shaped_level_set`
and is transported back by the linear map `diag(s, s, 1, 1)`. -/

namespace BirkhoffGlobalSection

namespace EHConvex

open MeasureTheory intervalIntegral Filter Topology Set

noncomputable section

/-- `sinh (s t) / s`, extended by `t` at `s = 0`. -/
def Sh (s t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, Real.cosh (s * τ)

/-- `sin (s t) / s`, extended by `t` at `s = 0`. -/
def Sn (s t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, Real.cos (s * τ)

theorem continuous_Sh : Continuous fun p : ℝ × ℝ => Sh p.1 p.2 := by
  unfold Sh
  exact continuous_parametric_intervalIntegral_of_continuous (μ := volume)
    (f := fun (p : ℝ × ℝ) (τ : ℝ) => Real.cosh (p.1 * τ)) (by fun_prop) continuous_snd

theorem continuous_Sn : Continuous fun p : ℝ × ℝ => Sn p.1 p.2 := by
  unfold Sn
  exact continuous_parametric_intervalIntegral_of_continuous (μ := volume)
    (f := fun (p : ℝ × ℝ) (τ : ℝ) => Real.cos (p.1 * τ)) (by fun_prop) continuous_snd

theorem mul_Sh (s t : ℝ) : s * Sh s t = Real.sinh (s * t) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  unfold Sh
  rw [intervalIntegral.integral_comp_mul_left (fun τ => Real.cosh τ) hs,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_sinh x)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [smul_eq_mul]
  field_simp

theorem mul_Sn (s t : ℝ) : s * Sn s t = Real.sin (s * t) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  unfold Sn
  rw [intervalIntegral.integral_comp_mul_left (fun τ => Real.cos τ) hs, integral_cos]
  simp [smul_eq_mul]
  field_simp

theorem Sh_zero (t : ℝ) : Sh 0 t = t := by simp [Sh]

theorem Sn_zero (t : ℝ) : Sn 0 t = t := by simp [Sn]

theorem hasDerivAt_Sh (s t : ℝ) : HasDerivAt (Sh s) (Real.cosh (s * t)) t :=
  intervalIntegral.integral_hasDerivAt_right (by
    apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.stronglyMeasurableAtFilter; fun_prop) (by fun_prop)

theorem hasDerivAt_Sn (s t : ℝ) : HasDerivAt (Sn s) (Real.cos (s * t)) t :=
  intervalIntegral.integral_hasDerivAt_right (by
    apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.stronglyMeasurableAtFilter; fun_prop) (by fun_prop)

/-- The position rescaling `diag(s, s, 1, 1)`. -/
def LscL (s : ℝ) : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi fun i => (if (i : ℕ) < 2 then s else 1) • ContinuousLinearMap.proj i

@[simp] theorem LscL_apply (s : ℝ) (y : Phase) (i : Fin 4) :
    LscL s y i = (if (i : ℕ) < 2 then s else 1) * y i := by
  simp only [LscL, ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem LscL_apply0 (s : ℝ) (y : Phase) : LscL s y 0 = s * y 0 := by simp
theorem LscL_apply1 (s : ℝ) (y : Phase) : LscL s y 1 = s * y 1 := by simp
theorem LscL_apply2 (s : ℝ) (y : Phase) : LscL s y 2 = y 2 := by simp
theorem LscL_apply3 (s : ℝ) (y : Phase) : LscL s y 3 = y 3 := by simp

theorem continuous_LscL : Continuous fun q : ℝ × Phase => LscL q.1 q.2 := by
  apply continuous_pi
  intro i
  simp only [LscL_apply]
  fin_cases i <;> simp <;> fun_prop

/-- The rescaled-energy term `c (cosh² x₁ - cos² x₂) / 4` with `x = s X`, `c = 1/s²`. -/
def Qs (s : ℝ) (y : Phase) : ℝ := (Sh s (y 0) ^ 2 + Sn s (y 1) ^ 2) / 4

/-- The rescaled EH Hamiltonian, continuous through `s = 0`. -/
def Grs (μ s : ℝ) (y : Phase) : ℝ := ehLeftHamiltonian μ 0 (LscL s y) + Qs s y

theorem Grs_eq {μ s : ℝ} (hs : s ≠ 0) (y : Phase) :
    Grs μ s y = ehLeftHamiltonian μ (1 / s ^ 2) (LscL s y) := by
  have h0 : Sh s (y 0) = Real.sinh (s * y 0) / s := by
    rw [eq_div_iff hs, mul_comm]; exact mul_Sh s (y 0)
  have h1 : Sn s (y 1) = Real.sin (s * y 1) / s := by
    rw [eq_div_iff hs, mul_comm]; exact mul_Sn s (y 1)
  unfold Grs Qs ehLeftHamiltonian
  simp only [LscL_apply0, LscL_apply1, LscL_apply2, LscL_apply3, h0, h1]
  have hc := Real.cosh_sq (s * y 0)
  have hs2 := Real.sin_sq_add_cos_sq (s * y 1)
  field_simp
  rw [hc]
  nlinarith [hs2]

/-- First derivative of the rescaled-energy term. -/
def qd (s : ℝ) (y v : Phase) : ℝ :=
  (Sh s (y 0) * Real.cosh (s * y 0) * v 0 + Sn s (y 1) * Real.cos (s * y 1) * v 1) / 2

/-- Second derivative of the rescaled-energy term along `v`. -/
def qh (s : ℝ) (y v : Phase) : ℝ :=
  ((Real.cosh (s * y 0) ^ 2 + Sh s (y 0) * (s * Real.sinh (s * y 0))) * v 0 ^ 2 +
    (Real.cos (s * y 1) ^ 2 - Sn s (y 1) * (s * Real.sin (s * y 1))) * v 1 ^ 2) / 2

theorem hasFDerivAt_Qs (s : ℝ) (y : Phase) :
    HasFDerivAt (Qs s)
      ((Sh s (y 0) * Real.cosh (s * y 0) / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0 +
        (Sn s (y 1) * Real.cos (s * y 1) / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1) y := by
  have h0 := (hasDerivAt_Sh s (y 0)).comp_hasFDerivAt y
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt
  have h1 := (hasDerivAt_Sn s (y 1)).comp_hasFDerivAt y
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).hasFDerivAt
  have hsum : HasFDerivAt (fun x : Phase => (Sh s ∘ ⇑(ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 4 => ℝ) 0)) x ^ 2 + (Sn s ∘ ⇑(ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 4 => ℝ) 1)) x ^ 2) _ y := (h0.pow 2).add (h1.pow 2)
  have := hsum.const_mul (1 / 4 : ℝ)
  have e : Qs s = fun x : Phase => (1 / 4 : ℝ) * ((Sh s ∘ ⇑(ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 4 => ℝ) 0)) x ^ 2 + (Sn s ∘ ⇑(ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 4 => ℝ) 1)) x ^ 2) := by
    funext x; simp [Qs]; ring
  rw [e]
  refine this.congr_fderiv ?_
  ext v
  simp
  ring

theorem fderiv_Qs_apply (s : ℝ) (y v : Phase) : fderiv ℝ (Qs s) y v = qd s y v := by
  rw [(hasFDerivAt_Qs s y).fderiv]
  simp [qd]
  ring

theorem hess_Qs (s : ℝ) (y v : Phase) :
    fderiv ℝ (fun x => fderiv ℝ (Qs s) x v) y v = qh s y v := by
  have e : (fun x => fderiv ℝ (Qs s) x v) = fun x => qd s x v := by
    funext x; exact fderiv_Qs_apply s x v
  rw [e]
  have p0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt (x := y)
  have p1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).hasFDerivAt (x := y)
  have a0 := (hasDerivAt_Sh s (y 0)).comp_hasFDerivAt y p0
  have a1 := (hasDerivAt_Sn s (y 1)).comp_hasFDerivAt y p1
  have b0 := (Real.hasDerivAt_cosh (s * y 0)).comp_hasFDerivAt y (p0.const_mul s)
  have b1 := (Real.hasDerivAt_cos (s * y 1)).comp_hasFDerivAt y (p1.const_mul s)
  have h := ((((a0.mul b0).mul_const (v 0)).add ((a1.mul b1).mul_const (v 1))).const_mul (1 / 2 : ℝ))
  have h' : HasFDerivAt (fun x : Phase => qd s x v) _ y :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp [qd]; ring)
  rw [h'.fderiv]
  simp [qh]
  ring

theorem differentiableAt_qd (s : ℝ) (v y : Phase) :
    DifferentiableAt ℝ (fun x : Phase => qd s x v) y := by
  unfold qd
  have p0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt (x := y)
  have p1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).hasFDerivAt (x := y)
  have a0 := ((hasDerivAt_Sh s (y 0)).comp_hasFDerivAt y p0).differentiableAt
  have a1 := ((hasDerivAt_Sn s (y 1)).comp_hasFDerivAt y p1).differentiableAt
  have b0 : DifferentiableAt ℝ (fun x : Phase => Real.cosh (s * x 0)) y := by fun_prop
  have b1 : DifferentiableAt ℝ (fun x : Phase => Real.cos (s * x 1)) y := by fun_prop
  have h := (((a0.mul b0).mul_const (v 0)).add ((a1.mul b1).mul_const (v 1))).mul_const (2⁻¹ : ℝ)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp; ring)

theorem contDiff_G0 (μ : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (ehLeftHamiltonian μ 0) := by
  unfold ehLeftHamiltonian; fun_prop

theorem hasFDerivAt_Grs (μ s : ℝ) (y : Phase) :
    HasFDerivAt (Grs μ s)
      ((fderiv ℝ (ehLeftHamiltonian μ 0) (LscL s y)).comp (LscL s) + fderiv ℝ (Qs s) y) y := by
  have hG := ((contDiff_G0 μ (n := 1)).differentiable one_ne_zero (LscL s y)).hasFDerivAt
  exact (hG.comp y (LscL s).hasFDerivAt).add (hasFDerivAt_Qs s y).differentiableAt.hasFDerivAt

theorem fderiv_Grs_apply (μ s : ℝ) (y v : Phase) :
    fderiv ℝ (Grs μ s) y v =
      fderiv ℝ Ghat (μ, 0, LscL s y) (L (LscL s v)) + qd s y v := by
  rw [(hasFDerivAt_Grs μ s y).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [fderiv_G_apply, fderiv_Qs_apply]

theorem hess_Grs (μ s : ℝ) (y v : Phase) :
    fderiv ℝ (fun x => fderiv ℝ (Grs μ s) x v) y v =
      fderiv ℝ (fderiv ℝ Ghat) (μ, 0, LscL s y) (L (LscL s v)) (L (LscL s v)) + qh s y v := by
  set w := LscL s v
  have e : (fun x => fderiv ℝ (Grs μ s) x v) =
      fun x => fderiv ℝ (ehLeftHamiltonian μ 0) (LscL s x) w + qd s x v := by
    funext x
    rw [(hasFDerivAt_Grs μ s x).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [fderiv_Qs_apply]
  rw [e]
  have hd1 : DifferentiableAt ℝ (fun z => fderiv ℝ (ehLeftHamiltonian μ 0) z w) (LscL s y) := by
    have h2 : ContDiff ℝ 2 (ehLeftHamiltonian μ 0) := contDiff_G0 μ
    have := ((h2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) (LscL s y)
    exact this.clm_apply (differentiableAt_const w)
  have hA := hd1.hasFDerivAt.comp y (LscL s).hasFDerivAt
  have hB := (differentiableAt_qd s v y).hasFDerivAt
  have hAB : HasFDerivAt (fun x => fderiv ℝ (ehLeftHamiltonian μ 0) (LscL s x) w + qd s x v)
      ((fderiv ℝ (fun z => fderiv ℝ (ehLeftHamiltonian μ 0) z w) (LscL s y)).comp (LscL s) +
        fderiv ℝ (fun x => qd s x v) y) y := hA.add hB
  rw [hAB.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
  have hq : fderiv ℝ (fun x : Phase => qd s x v) y v = qh s y v := by
    have := hess_Qs s y v
    rwa [show (fun x => fderiv ℝ (Qs s) x v) = fun x => qd s x v from
      funext fun x => fderiv_Qs_apply s x v] at this
  rw [hq, ← hess_G_eq]

/-- Along momentum directions the EH Hamiltonian is an explicit quadratic. -/
theorem fderiv_G0_mom (μ : ℝ) (x w : Phase) (hw0 : w 0 = 0) (hw1 : w 1 = 0) :
    fderiv ℝ (ehLeftHamiltonian μ 0) x w =
      (x 2 + Real.sin (2 * x 1) / 8) * w 2 + (x 3 + Real.sinh (2 * x 0) / 8) * w 3 := by
  have hd : DifferentiableAt ℝ (ehLeftHamiltonian μ 0) x :=
    (contDiff_G0 μ (n := 1)).differentiable one_ne_zero x
  rw [← hd.lineDeriv_eq_fderiv]
  set R := ehLeftHamiltonian μ 0 x - ((x 2 + Real.sin (2 * x 1) / 8) ^ 2 +
    (x 3 + Real.sinh (2 * x 0) / 8) ^ 2) / 2 with hR
  have e : (fun t : ℝ => ehLeftHamiltonian μ 0 (x + t • w)) = fun t =>
      ((x 2 + t * w 2 + Real.sin (2 * x 1) / 8) ^ 2 +
        (x 3 + t * w 3 + Real.sinh (2 * x 0) / 8) ^ 2) / 2 + R := by
    funext t
    rw [hR]
    unfold ehLeftHamiltonian
    simp [hw0, hw1]
    ring
  unfold lineDeriv
  rw [e]
  have hl : ∀ k : ℝ, HasDerivAt (fun t : ℝ => t * k) k 0 := fun k => by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const k
  have h := ((((hl (w 2)).const_add (x 2)).add_const (Real.sin (2 * x 1) / 8)).pow 2 |>.add
    ((((hl (w 3)).const_add (x 3)).add_const (Real.sinh (2 * x 0) / 8)).pow 2)).div_const 2
    |>.add_const R
  have h' : HasDerivAt (fun t : ℝ => ((x 2 + t * w 2 + Real.sin (2 * x 1) / 8) ^ 2 +
      (x 3 + t * w 3 + Real.sinh (2 * x 0) / 8) ^ 2) / 2 + R) _ 0 := h
  rw [h'.deriv]
  simp
  ring

theorem hess_G0_mom (μ : ℝ) (x w : Phase) (hw0 : w 0 = 0) (hw1 : w 1 = 0) :
    fderiv ℝ (fun z => fderiv ℝ (ehLeftHamiltonian μ 0) z w) x w = w 2 ^ 2 + w 3 ^ 2 := by
  have e : (fun z => fderiv ℝ (ehLeftHamiltonian μ 0) z w) = fun z : Phase =>
      (z 2 + Real.sin (2 * z 1) / 8) * w 2 + (z 3 + Real.sinh (2 * z 0) / 8) * w 3 := by
    funext z; exact fderiv_G0_mom μ z w hw0 hw1
  rw [e]
  have hd : DifferentiableAt ℝ (fun z : Phase =>
      (z 2 + Real.sin (2 * z 1) / 8) * w 2 + (z 3 + Real.sinh (2 * z 0) / 8) * w 3) x := by
    fun_prop
  rw [← hd.lineDeriv_eq_fderiv]
  unfold lineDeriv
  have e2 : (fun t : ℝ => (fun z : Phase =>
      (z 2 + Real.sin (2 * z 1) / 8) * w 2 + (z 3 + Real.sinh (2 * z 0) / 8) * w 3) (x + t • w)) =
      fun t => (x 2 + t * w 2 + Real.sin (2 * x 1) / 8) * w 2 +
        (x 3 + t * w 3 + Real.sinh (2 * x 0) / 8) * w 3 := by
    funext t; simp [hw0, hw1]
  rw [e2]
  have hl : ∀ k : ℝ, HasDerivAt (fun t : ℝ => t * k) k 0 := fun k => by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const k
  have h := ((((hl (w 2)).const_add (x 2)).add_const (Real.sin (2 * x 1) / 8)).mul_const (w 2)).add
    ((((hl (w 3)).const_add (x 3)).add_const (Real.sinh (2 * x 0) / 8)).mul_const (w 3))
  have h' : HasDerivAt (fun t : ℝ => (x 2 + t * w 2 + Real.sin (2 * x 1) / 8) * w 2 +
      (x 3 + t * w 3 + Real.sinh (2 * x 0) / 8) * w 3) _ 0 := h
  rw [h'.deriv]
  ring

theorem Grs_zero (μ : ℝ) (y : Phase) :
    Grs μ 0 y = (y 2 ^ 2 + y 3 ^ 2) / 2 + (y 0 ^ 2 + y 1 ^ 2) / 4 - (1 - μ) := by
  unfold Grs Qs ehLeftHamiltonian
  simp [Sh_zero, Sn_zero]
  ring

theorem radial_Grs_zero (μ : ℝ) (y : Phase) :
    fderiv ℝ (Grs μ 0) y y = y 2 ^ 2 + y 3 ^ 2 + (y 0 ^ 2 + y 1 ^ 2) / 2 := by
  rw [fderiv_Grs_apply, ← fderiv_G_apply, fderiv_G0_mom μ _ _ (by simp) (by simp)]
  simp [qd, Sh_zero, Sn_zero]
  ring

theorem hess_Grs_zero (μ : ℝ) (y v : Phase) :
    fderiv ℝ (fun x => fderiv ℝ (Grs μ 0) x v) y v =
      v 2 ^ 2 + v 3 ^ 2 + (v 0 ^ 2 + v 1 ^ 2) / 2 := by
  rw [hess_Grs, ← hess_G_eq, hess_G0_mom μ _ _ (by simp) (by simp)]
  simp [qh]

/-- `diag(s, s, 1, 1)` as a linear equivalence for `s ≠ 0`. -/
def LscE (s : ℝ) (hs : s ≠ 0) : Phase ≃L[ℝ] Phase :=
  ContinuousLinearEquiv.equivOfInverse (LscL s) (LscL s⁻¹)
    (fun y => by
      funext i; simp only [LscL_apply]
      split_ifs <;> field_simp)
    (fun y => by
      funext i; simp only [LscL_apply]
      split_ifs <;> field_simp)

@[simp] theorem LscE_apply (s : ℝ) (hs : s ≠ 0) (y : Phase) : LscE s hs y = LscL s y := rfl

/-- Second derivatives along a linear change of variables. -/
theorem hess_comp_clm {F : Phase → ℝ} (hF : ContDiff ℝ 2 F) (A : Phase →L[ℝ] Phase)
    (y w : Phase) :
    fderiv ℝ (fun x => fderiv ℝ (F ∘ A) x w) y w =
      fderiv ℝ (fun z => fderiv ℝ F z (A w)) (A y) (A w) := by
  have h1 : ∀ x, fderiv ℝ (F ∘ A) x w = fderiv ℝ F (A x) (A w) := by
    intro x
    have hd := (hF.differentiable (by norm_num) (A x)).hasFDerivAt
    rw [(hd.comp x A.hasFDerivAt).fderiv]
    rfl
  have e : (fun x => fderiv ℝ (F ∘ A) x w) = (fun z => fderiv ℝ F z (A w)) ∘ A := by
    funext x; exact h1 x
  rw [e]
  have hd : DifferentiableAt ℝ (fun z => fderiv ℝ F z (A w)) (A y) := by
    have := ((hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) (A y)
    exact this.clm_apply (differentiableAt_const _)
  rw [(hd.hasFDerivAt.comp y A.hasFDerivAt).fderiv]
  rfl

theorem fderiv_comp_clm {F : Phase → ℝ} (hF : ContDiff ℝ 1 F) (A : Phase →L[ℝ] Phase)
    (y w : Phase) : fderiv ℝ (F ∘ A) y w = fderiv ℝ F (A y) (A w) := by
  have hd := (hF.differentiable one_ne_zero (A y)).hasFDerivAt
  rw [(hd.comp y A.hasFDerivAt).fderiv]
  rfl

/-- Positive tangential Hessian transfers along a linear equivalence. -/
theorem tangentialHessian_of_comp {F : Phase → ℝ} (hF : ContDiff ℝ 2 F)
    (A : Phase ≃L[ℝ] Phase) {S : Set Phase}
    (h : ∀ s ∈ S, ∀ v : Phase, v ≠ 0 → fderiv ℝ (F ∘ A) s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ (F ∘ A) x v) s v) :
    HasPositiveTangentialHessianOn F (A '' S) := by
  refine ⟨fun z _ => hF.contDiffAt, ?_⟩
  rintro z ⟨s, hs, rfl⟩ v hv htan
  set w := A.symm v with hw
  have hAw : (A : Phase →L[ℝ] Phase) w = v := by simp [hw]
  have hw0 : w ≠ 0 := by
    intro h0; apply hv; rw [← hAw, h0, map_zero]
  have htan' : fderiv ℝ (F ∘ (A : Phase →L[ℝ] Phase)) s w = 0 := by
    rw [fderiv_comp_clm (hF.of_le (by norm_num)), hAw]; exact htan
  have := h s hs w hw0 htan'
  have e : (F ∘ ⇑A) = (F ∘ ⇑(A : Phase →L[ℝ] Phase)) := rfl
  rw [e, hess_comp_clm hF, hAw] at this
  exact this

/-- A component missing the faces of a box and starting in its open core stays
in the core. -/
theorem component_subset_of_faces {G : Phase → ℝ} {B Bc : Set Phase} (hB : IsClosed B)
    (hBc : IsOpen Bc) (hsub : Bc ⊆ B) (hfaces : ∀ s ∈ B ∩ Bcᶜ, 0 < G s) {p : Phase}
    (hp : G p = 0) (hpc : p ∈ Bc) :
    connectedComponentIn {s | G s = 0} p ⊆ Bc := by
  have hpre := isPreconnected_connectedComponentIn (F := {s : Phase | G s = 0}) (x := p)
  have hsub' : connectedComponentIn {s | G s = 0} p ⊆ Bc ∪ Bᶜ := by
    intro s hs
    have hz : G s = 0 := by
      have h := connectedComponentIn_subset {s : Phase | G s = 0} p
      exact h hs
    by_contra hn
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hn
    have := hfaces s ⟨hn.2, hn.1⟩
    linarith
  exact hpre.subset_left_of_subset_union hBc hB.isOpen_compl
    (disjoint_compl_right_iff_subset.mpr hsub) hsub'
    ⟨p, mem_connectedComponentIn hp, hpc⟩

theorem Grs_eq_Ghat (μ s : ℝ) (y : Phase) :
    Grs μ s y = Ghat (μ, 0, LscL s y) + Qs s y := rfl

theorem continuous_Grs : Continuous fun q : (ℝ × ℝ) × Phase => Grs q.1.1 q.1.2 q.2 := by
  simp only [Grs_eq_Ghat, Qs]
  have hL : Continuous fun q : (ℝ × ℝ) × Phase => LscL q.1.2 q.2 :=
    continuous_LscL.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hG : Continuous fun q : (ℝ × ℝ) × Phase => Ghat (q.1.1, 0, LscL q.1.2 q.2) :=
    continuous_Ghat.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_const.prodMk hL))
  have hS : Continuous fun q : (ℝ × ℝ) × Phase => Sh q.1.2 (q.2 0) :=
    continuous_Sh.comp ((continuous_snd.comp continuous_fst).prodMk (by fun_prop))
  have hN : Continuous fun q : (ℝ × ℝ) × Phase => Sn q.1.2 (q.2 1) :=
    continuous_Sn.comp ((continuous_snd.comp continuous_fst).prodMk (by fun_prop))
  exact hG.add (((hS.pow 2).add (hN.pow 2)).div_const 4)

attribute [local irreducible] Grs

theorem Grs_at_zero (μ s : ℝ) : Grs μ s 0 = μ - 1 := by
  unfold Grs Qs
  simp [Sh, Sn, map_zero]
  unfold ehLeftHamiltonian
  simp
  ring

theorem LscL_collision (μ s : ℝ) : LscL s (ehLeftCollisionPoint μ) = ehLeftCollisionPoint μ := by
  funext i; fin_cases i <;> simp [ehLeftCollisionPoint]

theorem Grs_collision (μ s : ℝ) (hμ : μ ≤ 1) : Grs μ s (ehLeftCollisionPoint μ) = 0 := by
  unfold Grs Qs
  rw [LscL_collision, G_collision μ 0 hμ]
  simp [ehLeftCollisionPoint, Sh, Sn]

theorem collision_mem_ball {μ : ℝ} (hμ : 0 < μ) :
    ehLeftCollisionPoint μ ∈ Metric.ball (0 : Phase) 2 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)]
  have h1 : Real.sqrt (1 - μ) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have h2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  intro i
  fin_cases i <;> simp [ehLeftCollisionPoint]
  have h3 : |Real.sqrt (1 - μ)| ≤ 1 := by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact h1
  have h4 : |Real.sqrt 2| < 2 := by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact h2
  nlinarith [abs_nonneg (Real.sqrt 2), abs_nonneg (Real.sqrt (1 - μ))]

theorem Grs_pos_on_sphere (y : Phase) (hy : y ∈ Metric.closedBall (0 : Phase) 2 ∩
    (Metric.ball (0 : Phase) 2)ᶜ) : 0 < Grs (1 / 2) 0 y := by
  rw [Grs_zero]
  obtain ⟨_, hy2⟩ := hy
  rw [mem_compl_iff, mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)] at hy2
  push_neg at hy2
  obtain ⟨i, hi⟩ := hy2
  rw [Real.norm_eq_abs] at hi
  have hsq : 4 ≤ y i ^ 2 := by nlinarith [abs_nonneg (y i), sq_abs (y i)]
  have h0 := sq_nonneg (y 0); have h1 := sq_nonneg (y 1)
  have h2 := sq_nonneg (y 2); have h3 := sq_nonneg (y 3)
  fin_cases i <;> simp at hsq <;> nlinarith

theorem eventually_faces_r :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, 0),
      ∀ y ∈ Metric.closedBall (0 : Phase) 2 ∩ (Metric.ball (0 : Phase) 2)ᶜ, 0 < Grs p.1 p.2 y := by
  have h := tube_pos_of_compact (P := ℝ × ℝ) (E := Phase)
    ((isCompact_closedBall (0 : Phase) 2).inter_right Metric.isOpen_ball.isClosed_compl)
    (C := Set.univ) isClosed_univ (Φ := fun q => Grs q.1.1 q.1.2 q.2) continuous_Grs
    (p₀ := ((1 : ℝ) / 2, 0)) (fun y hy _ => Grs_pos_on_sphere y hy)
  filter_upwards [h] with p hp y hy using hp y hy trivial

theorem continuous_star_r : Continuous fun q : (ℝ × ℝ) × Phase =>
    fderiv ℝ Ghat (q.1.1, 0, LscL q.1.2 q.2) (L (LscL q.1.2 q.2)) + qd q.1.2 q.2 q.2 := by
  have hL : Continuous fun q : (ℝ × ℝ) × Phase => LscL q.1.2 q.2 :=
    continuous_LscL.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hA : Continuous fun q : (ℝ × ℝ) × Phase =>
      fderiv ℝ Ghat (q.1.1, 0, LscL q.1.2 q.2) (L (LscL q.1.2 q.2)) :=
    (continuous_fderiv_Ghat.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_const.prodMk hL))).clm_apply (L.continuous.comp hL)
  have hS : Continuous fun q : (ℝ × ℝ) × Phase => Sh q.1.2 (q.2 0) :=
    continuous_Sh.comp ((continuous_snd.comp continuous_fst).prodMk (by fun_prop))
  have hN : Continuous fun q : (ℝ × ℝ) × Phase => Sn q.1.2 (q.2 1) :=
    continuous_Sn.comp ((continuous_snd.comp continuous_fst).prodMk (by fun_prop))
  unfold qd
  exact hA.add ((((hS.mul (by fun_prop)).mul (by fun_prop)).add
    ((hN.mul (by fun_prop)).mul (by fun_prop))).div_const 2)

theorem eventually_star_r :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, 0),
      ∀ y ∈ Metric.closedBall (0 : Phase) 2, Grs p.1 p.2 y = 0 →
        0 < fderiv ℝ (Grs p.1 p.2) y y := by
  have h := tube_pos_of_compact (P := ℝ × ℝ) (E := Phase) (isCompact_closedBall (0 : Phase) 2)
    (C := {q | Grs q.1.1 q.1.2 q.2 = 0}) (isClosed_eq continuous_Grs continuous_const)
    (Φ := fun q => fderiv ℝ Ghat (q.1.1, 0, LscL q.1.2 q.2) (L (LscL q.1.2 q.2)) +
      qd q.1.2 q.2 q.2) continuous_star_r (p₀ := ((1 : ℝ) / 2, 0))
    (fun y _ hz => by
      simp only [mem_setOf_eq] at hz
      rw [← fderiv_Grs_apply, radial_Grs_zero]
      rw [Grs_zero] at hz
      nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)])
  filter_upwards [h] with p hp y hy hz
  rw [fderiv_Grs_apply]
  exact hp y hy hz

theorem eventually_hess_r :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, 0),
      ∀ y ∈ Metric.closedBall (0 : Phase) 2 ×ˢ Metric.sphere (0 : Phase) 1,
        (Grs p.1 p.2 y.1 = 0 ∧ fderiv ℝ (Grs p.1 p.2) y.1 y.2 = 0) →
        0 < fderiv ℝ (fun x => fderiv ℝ (Grs p.1 p.2) x y.2) y.1 y.2 := by
  have hL1 : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) => LscL q.1.2 q.2.1 :=
    continuous_LscL.comp ((continuous_snd.comp continuous_fst).prodMk (by fun_prop))
  have hL2 : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) => LscL q.1.2 q.2.2 :=
    continuous_LscL.comp ((continuous_snd.comp continuous_fst).prodMk (by fun_prop))
  have hP : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) =>
      ((q.1.1, 0, LscL q.1.2 q.2.1) : ℝ × ℝ × Phase) :=
    (continuous_fst.comp continuous_fst).prodMk (continuous_const.prodMk hL1)
  have hS : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) => Sh q.1.2 (q.2.1 0) :=
    continuous_Sh.comp ((continuous_snd.comp continuous_fst).prodMk (by fun_prop))
  have hN : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) => Sn q.1.2 (q.2.1 1) :=
    continuous_Sn.comp ((continuous_snd.comp continuous_fst).prodMk (by fun_prop))
  have hGrs : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) => Grs q.1.1 q.1.2 q.2.1 :=
    continuous_Grs.comp ((continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  have htan : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) =>
      fderiv ℝ Ghat (q.1.1, 0, LscL q.1.2 q.2.1) (L (LscL q.1.2 q.2.2)) + qd q.1.2 q.2.1 q.2.2 := by
    unfold qd
    exact ((continuous_fderiv_Ghat.comp hP).clm_apply (L.continuous.comp hL2)).add
      ((((hS.mul (by fun_prop)).mul (by fun_prop)).add
        ((hN.mul (by fun_prop)).mul (by fun_prop))).div_const 2)
  have hhess : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) =>
      fderiv ℝ (fderiv ℝ Ghat) (q.1.1, 0, LscL q.1.2 q.2.1) (L (LscL q.1.2 q.2.2))
        (L (LscL q.1.2 q.2.2)) + qh q.1.2 q.2.1 q.2.2 := by
    unfold qh
    exact (((continuous_fderiv2_Ghat.comp hP).clm_apply (L.continuous.comp hL2)).clm_apply
      (L.continuous.comp hL2)).add
      (((((by fun_prop : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) =>
          Real.cosh (q.1.2 * q.2.1 0) ^ 2).add (hS.mul (by fun_prop))).mul (by fun_prop)).add
        (((by fun_prop : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) =>
          Real.cos (q.1.2 * q.2.1 1) ^ 2).sub (hN.mul (by fun_prop))).mul (by fun_prop))).div_const 2)
  have h := tube_pos_of_compact (P := ℝ × ℝ) (E := Phase × Phase)
    ((isCompact_closedBall (0 : Phase) 2).prod (isCompact_sphere 0 1))
    (C := {q | Grs q.1.1 q.1.2 q.2.1 = 0 ∧
      fderiv ℝ Ghat (q.1.1, 0, LscL q.1.2 q.2.1) (L (LscL q.1.2 q.2.2)) + qd q.1.2 q.2.1 q.2.2 = 0})
    ((isClosed_eq hGrs continuous_const).inter (isClosed_eq htan continuous_const))
    (Φ := fun q => fderiv ℝ (fderiv ℝ Ghat) (q.1.1, 0, LscL q.1.2 q.2.1) (L (LscL q.1.2 q.2.2))
        (L (LscL q.1.2 q.2.2)) + qh q.1.2 q.2.1 q.2.2) hhess (p₀ := ((1 : ℝ) / 2, 0))
    (fun y hy _ => by
      obtain ⟨_, hsph⟩ := hy
      rw [← hess_Grs, hess_Grs_zero]
      have hv : y.2 ≠ 0 := by
        intro h0; rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hsph; norm_num at hsph
      have hpos : 0 < y.2 0 ^ 2 + y.2 1 ^ 2 + y.2 2 ^ 2 + y.2 3 ^ 2 := by
        by_contra hc
        apply hv
        funext i
        have := sq_nonneg (y.2 0); have := sq_nonneg (y.2 1)
        have := sq_nonneg (y.2 2); have := sq_nonneg (y.2 3)
        fin_cases i <;> simp <;> nlinarith
      nlinarith [sq_nonneg (y.2 0), sq_nonneg (y.2 1), sq_nonneg (y.2 2), sq_nonneg (y.2 3)])
  filter_upwards [h] with p hp y hy hC
  rw [hess_Grs]
  exact hp y hy ⟨hC.1, by rw [← fderiv_Grs_apply]; exact hC.2⟩

theorem closedBall_smul : ∀ y ∈ Metric.closedBall (0 : Phase) 2, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    t • y ∈ Metric.closedBall (0 : Phase) 2 := by
  intro y hy t ht0 ht1
  rw [mem_closedBall_zero_iff] at hy ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  nlinarith [norm_nonneg y]

/-- One parameter of the tail: convex body of the rescaled zero level, transported back. -/
theorem tail_body {μ s : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hs : s ≠ 0)
    (hfaces : ∀ y ∈ Metric.closedBall (0 : Phase) 2 ∩ (Metric.ball (0 : Phase) 2)ᶜ,
      0 < Grs μ s y)
    (hstar : ∀ y ∈ Metric.closedBall (0 : Phase) 2, Grs μ s y = 0 →
      0 < fderiv ℝ (Grs μ s) y y)
    (hhess : ∀ y ∈ Metric.closedBall (0 : Phase) 2 ×ˢ Metric.sphere (0 : Phase) 1,
      (Grs μ s y.1 = 0 ∧ fderiv ℝ (Grs μ s) y.1 y.2 = 0) →
      0 < fderiv ℝ (fun x => fderiv ℝ (Grs μ s) x y.2) y.1 y.2) :
    ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧ (0 : Phase) ∈ interior B ∧
      ehLeftEnergyComponent μ (1 / s ^ 2) = frontier B ∧
      HasPositiveTangentialHessianOn (ehLeftHamiltonian μ (1 / s ^ 2)) (frontier B) := by
  set c := 1 / s ^ 2
  set A := LscE s hs
  have hG2 : ContDiff ℝ 2 (ehLeftHamiltonian μ c) := by unfold ehLeftHamiltonian; fun_prop
  have hGA : Grs μ s = ehLeftHamiltonian μ c ∘ ⇑A := by
    funext y; exact Grs_eq hs y
  have hGrs2 : ContDiff ℝ 2 (Grs μ s) := by rw [hGA]; exact hG2.comp A.contDiff
  set p := ehLeftCollisionPoint μ
  have hp : Grs μ s p = 0 := Grs_collision μ s hμ1.le
  have hpc : p ∈ Metric.ball (0 : Phase) 2 := collision_mem_ball hμ0
  set S := connectedComponentIn {y | Grs μ s y = 0} p with hSdef
  have hScore : S ⊆ Metric.ball (0 : Phase) 2 :=
    component_subset_of_faces Metric.isClosed_closedBall Metric.isOpen_ball
      Metric.ball_subset_closedBall hfaces hp hpc
  have hSB : S ⊆ Metric.closedBall (0 : Phase) 2 := hScore.trans Metric.ball_subset_closedBall
  have hS0 : ∀ y ∈ S, Grs μ s y = 0 := by
    intro y hy
    have h := connectedComponentIn_subset {y : Phase | Grs μ s y = 0} p
    exact h hy
  have hneg0 : Grs μ s 0 < 0 := by rw [Grs_at_zero]; linarith
  obtain ⟨hray, huniq, hneg⟩ := radial_graph_generic (G := Grs μ s) (hGrs2.of_le (by norm_num))
    (isCompact_closedBall 0 2) Metric.isOpen_ball Metric.ball_subset_closedBall closedBall_smul
    hneg0 hfaces hstar hp (Metric.ball_subset_closedBall hpc) hSB
  have hSc : IsCompact S :=
    (isCompact_closedBall (0 : Phase) 2).of_isClosed_subset
      (isClosed_connectedComponentIn_of_isClosed
        (isClosed_eq hGrs2.continuous continuous_const) p) hSB
  have hreg : ∀ y ∈ S, fderiv ℝ (Grs μ s) y ≠ 0 := by
    intro y hy hd
    have := hstar y (hSB hy) (hS0 y hy)
    rw [hd] at this; simp at this
  have hhessS : ∀ y ∈ S, ∀ v : Phase, v ≠ 0 → fderiv ℝ (Grs μ s) y v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ (Grs μ s) x v) y v := by
    intro y hy v hv htan
    set t : ℝ := ‖v‖⁻¹ with ht
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have htpos : 0 < t := inv_pos.mpr hnv
    have hw : t • v ∈ Metric.sphere (0 : Phase) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht,
        inv_mul_cancel₀ hnv.ne']
    have htan' : fderiv ℝ (Grs μ s) y (t • v) = 0 := by rw [map_smul, htan, smul_zero]
    have := hhess (y, t • v) ⟨hSB hy, hw⟩ ⟨hS0 y hy, htan'⟩
    simp only at this
    have e : (fun x => fderiv ℝ (Grs μ s) x (t • v)) = fun x => t • fderiv ℝ (Grs μ s) x v := by
      funext x; rw [map_smul]
    have hd : DifferentiableAt ℝ (fun x => fderiv ℝ (Grs μ s) x v) y := by
      have := ((hGrs2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y
      exact this.clm_apply (differentiableAt_const v)
    have hc : HasFDerivAt (fun x => t • fderiv ℝ (Grs μ s) x v)
        (t • fderiv ℝ (fun x => fderiv ℝ (Grs μ s) x v) y) y := hd.hasFDerivAt.const_smul t
    rw [e, hc.fderiv] at this
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul] at this
    have h2 : 0 < t * t := mul_pos htpos htpos
    nlinarith
  obtain ⟨Bh, hBc, hBconv, hB0, hBS⟩ := convex_body_of_star_shaped_level_set (Grs μ s) S hSc hS0
    hreg ⟨fun y _ => hGrs2.contDiffAt, hhessS⟩ (fun x hx => hray x hx)
    (fun x hx r t hr ht h1 h2 => huniq x hx r t hr ht h1 h2)
    (fun x hx R hR h r hr hrR => hneg x hx R hR h r hr hrR)
  refine ⟨A '' Bh, hBc.image A.continuous, hBconv.linear_image (A : Phase →L[ℝ] Phase).toLinearMap,
    ?_, ?_, ?_⟩
  · change (0 : Phase) ∈ interior (A.toHomeomorph '' Bh)
    rw [← A.toHomeomorph.image_interior]
    exact ⟨0, hB0, map_zero A⟩
  · have hcomp : A '' S = ehLeftEnergyComponent μ c := by
      have h := A.toHomeomorph.image_connectedComponentIn (s := {y | Grs μ s y = 0}) (x := p)
        (show p ∈ {y | Grs μ s y = 0} from hp)
      have himg : A.toHomeomorph '' {y | Grs μ s y = 0} = {z | ehLeftHamiltonian μ c z = 0} := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          simp only [mem_setOf_eq] at hy ⊢
          rw [hGA] at hy; exact hy
        · intro hz
          refine ⟨A.symm z, ?_, by simp⟩
          simp only [mem_setOf_eq] at hz ⊢
          rw [hGA]; simpa using hz
      have hAp : A.toHomeomorph p = p := LscL_collision μ s
      rw [himg, hAp] at h
      exact h
    rw [← hcomp, hBS]
    exact A.toHomeomorph.image_frontier Bh
  · change HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier (A.toHomeomorph '' Bh))
    rw [← A.toHomeomorph.image_frontier Bh, ← hBS]
    apply tangentialHessian_of_comp hG2 A
    intro y hy v hv htan
    rw [← hGA] at htan ⊢
    exact hhessS y hy v hv htan

theorem low_energy_tail :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B ∧
          HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier B) := by
  have hev := (eventually_faces_r.and eventually_star_r).and eventually_hess_r
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hev⟩ := hev
  refine ⟨δ, 4 / δ ^ 2 + 1, hδ, fun μ c hμ0 hμ1 hμ hc _ => ?_⟩
  have hcpos : 0 < c := by have : 0 ≤ 4 / δ ^ 2 := by positivity
                           linarith
  set s := 1 / Real.sqrt c with hs
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hcpos.le
  have hspos : 0 < s := by rw [hs]; positivity
  have hcs : 1 / s ^ 2 = c := by rw [hs, div_pow, one_pow, one_div_one_div, hsq]
  have hsδ : s < δ := by
    rw [hs, div_lt_iff₀ (Real.sqrt_pos.mpr hcpos)]
    have h1 : 4 / δ ^ 2 < c := by linarith
    have h2 : (2 / δ) ^ 2 < Real.sqrt c ^ 2 := by
      rw [hsq, div_pow]; linarith
    have h3 : 2 / δ < Real.sqrt c := by
      by_contra hn
      push_neg at hn
      have h0 : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
      nlinarith
    have h4 : 2 / δ * δ = 2 := by field_simp
    nlinarith
  have hdist : dist ((μ, s) : ℝ × ℝ) ((1 : ℝ) / 2, 0) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hspos]
    exact max_lt hμ hsδ
  obtain ⟨⟨hf, hst⟩, hh⟩ := hev hdist
  have := tail_body hμ0 hμ1 hspos.ne' hf hst hh
  rwa [hcs] at this

end

end EHConvex

end BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B ∧
          HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier B) :=
  EHConvex.low_energy_tail
