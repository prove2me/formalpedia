-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.leviCivita_explicit_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:55:30.679988+00:00
-- url     : https://prove2.me/submissions/5c7e60b0-f2c4-4b99-ad3a-7b31baa75975

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Filter Topology

noncomputable section

/-! ## A gradient calculus on `Phase` -/

/-- The linear functional `v ↦ g ⬝ᵥ v`. -/
def gradCLM (g : Phase) : Phase →L[ℝ] ℝ :=
  ∑ i : Fin 4, g i • ContinuousLinearMap.proj i

@[simp] theorem gradCLM_apply (g v : Phase) : gradCLM g v = g ⬝ᵥ v := by
  simp [gradCLM, dotProduct]

/-- `f` has gradient `g` at `s`. -/
def HasGradAt (f : Phase → ℝ) (g s : Phase) : Prop :=
  HasFDerivAt f (gradCLM g) s

namespace HasGradAt

variable {f h : Phase → ℝ} {g k s : Phase}

theorem congr_grad (hf : HasGradAt f g s) (e : g = k) : HasGradAt f k s := e ▸ hf

theorem const (a : ℝ) (s : Phase) : HasGradAt (fun _ => a) 0 s := by
  have : gradCLM 0 = 0 := ContinuousLinearMap.ext fun v => by simp
  unfold HasGradAt; rw [this]; exact hasFDerivAt_const a s

theorem coord (i : Fin 4) (s : Phase) : HasGradAt (fun x => x i) (Pi.single i 1) s := by
  have : gradCLM (Pi.single i 1) = ContinuousLinearMap.proj i :=
    ContinuousLinearMap.ext fun v => by simp [dotProduct, Pi.single_apply]
  unfold HasGradAt; rw [this]; exact hasFDerivAt_apply i s

theorem add (hf : HasGradAt f g s) (hh : HasGradAt h k s) :
    HasGradAt (fun x => f x + h x) (g + k) s := by
  have : gradCLM (g + k) = gradCLM g + gradCLM k :=
    ContinuousLinearMap.ext fun v => by simp [add_dotProduct]
  unfold HasGradAt; rw [this]; exact HasFDerivAt.add hf hh

theorem neg (hf : HasGradAt f g s) : HasGradAt (fun x => -f x) (-g) s := by
  have : gradCLM (-g) = -gradCLM g := ContinuousLinearMap.ext fun v => by simp
  unfold HasGradAt; rw [this]; exact HasFDerivAt.neg hf

theorem sub (hf : HasGradAt f g s) (hh : HasGradAt h k s) :
    HasGradAt (fun x => f x - h x) (g - k) s := by
  have : gradCLM (g - k) = gradCLM g - gradCLM k :=
    ContinuousLinearMap.ext fun v => by simp [sub_dotProduct]
  unfold HasGradAt; rw [this]; exact HasFDerivAt.sub hf hh

theorem mul (hf : HasGradAt f g s) (hh : HasGradAt h k s) :
    HasGradAt (fun x => f x * h x) (f s • k + h s • g) s := by
  have : gradCLM (f s • k + h s • g) = f s • gradCLM k + h s • gradCLM g :=
    ContinuousLinearMap.ext fun v => by simp [add_dotProduct]
  unfold HasGradAt; rw [this]; exact HasFDerivAt.mul hf hh

theorem pow (hf : HasGradAt f g s) (n : ℕ) :
    HasGradAt (fun x => f x ^ n) ((n * f s ^ (n - 1)) • g) s := by
  have : gradCLM ((n * f s ^ (n - 1)) • g) = (n • f s ^ (n - 1)) • gradCLM g :=
    ContinuousLinearMap.ext fun v => by simp [nsmul_eq_mul]
  unfold HasGradAt; rw [this]; exact HasFDerivAt.pow hf n

theorem inv (hf : HasGradAt f g s) (hs : f s ≠ 0) :
    HasGradAt (fun x => (f x)⁻¹) ((-(f s ^ 2)⁻¹) • g) s := by
  have : gradCLM ((-(f s ^ 2)⁻¹) • g) = (-(f s ^ 2)⁻¹) • gradCLM g :=
    ContinuousLinearMap.ext fun v => by simp
  unfold HasGradAt; rw [this]; exact (hasDerivAt_inv hs).comp_hasFDerivAt s hf

theorem div (hf : HasGradAt f g s) (hh : HasGradAt h k s) (hs : h s ≠ 0) :
    HasGradAt (fun x => f x / h x) (f s • ((-(h s ^ 2)⁻¹) • k) + (h s)⁻¹ • g) s := by
  simpa only [div_eq_mul_inv] using hf.mul (hh.inv hs)

theorem sqrt (hf : HasGradAt f g s) (hs : 0 < f s) :
    HasGradAt (fun x => Real.sqrt (f x)) ((1 / (2 * Real.sqrt (f s))) • g) s := by
  have : gradCLM ((1 / (2 * Real.sqrt (f s))) • g) =
      (1 / (2 * Real.sqrt (f s))) • gradCLM g :=
    ContinuousLinearMap.ext fun v => by simp
  unfold HasGradAt; rw [this]
  exact (Real.hasDerivAt_sqrt hs.ne').comp_hasFDerivAt s hf

theorem hasFDerivAt (hf : HasGradAt f g s) : HasFDerivAt f (gradCLM g) s := hf

theorem differentiableAt (hf : HasGradAt f g s) : DifferentiableAt ℝ f s :=
  hf.hasFDerivAt.differentiableAt

theorem fderiv_eq (hf : HasGradAt f g s) : fderiv ℝ f s = gradCLM g :=
  hf.hasFDerivAt.fderiv

end HasGradAt

theorem continuous_secondCollisionDistanceSq : Continuous secondCollisionDistanceSq := by
  unfold secondCollisionDistanceSq; fun_prop

theorem isOpen_U : IsOpen U :=
  isOpen_lt continuous_const continuous_secondCollisionDistanceSq

theorem rD_pos {s : Phase} (hs : s ∈ U) : 0 < rD s := Real.sqrt_pos.mpr hs

theorem continuous_rD : Continuous rD :=
  Real.continuous_sqrt.comp continuous_secondCollisionDistanceSq

theorem leviCivitaHamiltonian_eq_pP (μ c : ℝ) (s : Phase) :
    leviCivitaHamiltonian μ c s = pP μ c s - μ * (zNormSq s / rD s) := by
  unfold leviCivitaHamiltonian pP rD; ring

theorem hasGradAt_zNormSq (s : Phase) : HasGradAt zNormSq (dZ s) s := by
  show HasGradAt (fun x => x 0 ^ 2 + x 1 ^ 2) _ s
  apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
  funext l; fin_cases l <;> simp [dZ]

theorem hasGradAt_secondCollisionDistanceSq (s : Phase) :
    HasGradAt secondCollisionDistanceSq (dD s) s := by
  show HasGradAt (fun x => (2 * (x 0 ^ 2 - x 1 ^ 2) - 1) ^ 2 + (4 * x 0 * x 1) ^ 2) _ s
  apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
  funext l; fin_cases l <;> simp [dD] <;> ring

theorem hasGradAt_rD {s : Phase} (hs : s ∈ U) :
    HasGradAt rD ((1 / (2 * rD s)) • dD s) s :=
  (hasGradAt_secondCollisionDistanceSq s).sqrt hs

theorem hasGradAt_pP (μ c : ℝ) (s : Phase) : HasGradAt (pP μ c) (dP μ c s) s := by
  show HasGradAt (fun x => (x 2 ^ 2 + x 3 ^ 2) / 2 + c * (x 0 ^ 2 + x 1 ^ 2) - (1 - μ) / 2
    + 2 * (x 0 ^ 2 + x 1 ^ 2) * (x 0 * x 3 - x 1 * x 2) - μ * (x 0 * x 3 + x 1 * x 2)) _ s
  apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul]; norm_num)
  funext l; fin_cases l <;> simp [dP] <;> ring

/-- `K` has gradient `kGrad` on `U`. -/
theorem hasGradAt_leviCivitaHamiltonian (μ c : ℝ) {s : Phase} (hs : s ∈ U) :
    HasGradAt (leviCivitaHamiltonian μ c) (kGrad μ c s) s := by
  have hr := rD_pos hs
  have e : leviCivitaHamiltonian μ c = fun x => pP μ c x - μ * (zNormSq x / rD x) :=
    funext (leviCivitaHamiltonian_eq_pP μ c)
  rw [e]
  apply HasGradAt.congr_grad
    ((hasGradAt_pP μ c s).sub ((HasGradAt.const μ s).mul
      ((hasGradAt_zNormSq s).div (hasGradAt_rD hs) hr.ne')))
  funext l
  simp only [kGrad, kGradR, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  field_simp
  ring

theorem hasGradAt_dZ (s : Phase) (k : Fin 4) :
    HasGradAt (fun x => dZ x k) (fun l => hZ k l) s := by
  fin_cases k
  · show HasGradAt (fun x => 2 * x 0) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hZ]
  · show HasGradAt (fun x => 2 * x 1) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hZ]
  · show HasGradAt (fun _ => (0 : ℝ)) _ s
    apply HasGradAt.congr_grad (HasGradAt.const 0 s)
    funext l; fin_cases l <;> simp [hZ]
  · show HasGradAt (fun _ => (0 : ℝ)) _ s
    apply HasGradAt.congr_grad (HasGradAt.const 0 s)
    funext l; fin_cases l <;> simp [hZ]

theorem hasGradAt_dD (s : Phase) (k : Fin 4) :
    HasGradAt (fun x => dD x k) (fun l => hD s k l) s := by
  fin_cases k
  · show HasGradAt (fun x => 16 * x 0 ^ 3 + 16 * x 0 * x 1 ^ 2 - 8 * x 0) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hD] <;> ring
  · show HasGradAt (fun x => 16 * x 0 ^ 2 * x 1 + 16 * x 1 ^ 3 + 8 * x 1) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hD] <;> ring
  · show HasGradAt (fun _ => (0 : ℝ)) _ s
    apply HasGradAt.congr_grad (HasGradAt.const 0 s)
    funext l; fin_cases l <;> simp [hD]
  · show HasGradAt (fun _ => (0 : ℝ)) _ s
    apply HasGradAt.congr_grad (HasGradAt.const 0 s)
    funext l; fin_cases l <;> simp [hD]

theorem hasGradAt_dP (μ c : ℝ) (s : Phase) (k : Fin 4) :
    HasGradAt (fun x => dP μ c x k) (fun l => hP μ c s k l) s := by
  fin_cases k
  · show HasGradAt (fun x => 2 * c * x 0 - μ * x 3 - 4 * x 2 * x 0 * x 1
      + 6 * x 3 * x 0 ^ 2 + 2 * x 3 * x 1 ^ 2) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hP] <;> ring
  · show HasGradAt (fun x => 2 * c * x 1 - μ * x 2 - 2 * x 2 * x 0 ^ 2
      - 6 * x 2 * x 1 ^ 2 + 4 * x 3 * x 0 * x 1) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hP] <;> ring
  · show HasGradAt (fun x => -μ * x 1 + x 2 - 2 * x 0 ^ 2 * x 1 - 2 * x 1 ^ 3) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hP] <;> ring
  · show HasGradAt (fun x => -μ * x 0 + x 3 + 2 * x 0 ^ 3 + 2 * x 0 * x 1 ^ 2) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.sqrt, HasGradAt.pow, HasGradAt.div, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hP] <;> ring

/-- Each component of `kGrad` has gradient the corresponding row of `kHess` on `U`. -/
theorem hasGradAt_kGrad (μ c : ℝ) {s : Phase} (hs : s ∈ U) (k : Fin 4) :
    HasGradAt (fun x => kGrad μ c x k) (fun l => kHess μ c s k l) s := by
  have hr := rD_pos hs
  show HasGradAt (fun x => dP μ c x k - μ * (dZ x k / rD x
    - zNormSq x * dD x k / (2 * rD x ^ 3))) _ s
  apply HasGradAt.congr_grad
    ((hasGradAt_dP μ c s k).sub ((HasGradAt.const μ s).mul
      (((hasGradAt_dZ s k).div (hasGradAt_rD hs) hr.ne').sub
        (((hasGradAt_zNormSq s).mul (hasGradAt_dD s k)).div
          ((HasGradAt.const 2 s).mul ((hasGradAt_rD hs).pow 3)) (by positivity)))))
  funext l
  simp only [kHess, kHessR, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  field_simp
  push_cast
  ring

theorem fderiv_leviCivitaHamiltonian (μ c : ℝ) {s : Phase} (hs : s ∈ U) :
    fderiv ℝ (leviCivitaHamiltonian μ c) s = gradCLM (kGrad μ c s) :=
  (hasGradAt_leviCivitaHamiltonian μ c hs).fderiv_eq

theorem partialDerivative_eq_kGrad (μ c : ℝ) {s : Phase} (hs : s ∈ U) (i : Fin 4) :
    partialDerivative (leviCivitaHamiltonian μ c) s i = kGrad μ c s i := by
  simp [partialDerivative, fderiv_leviCivitaHamiltonian μ c hs, dotProduct,
    coordinateVector]

/-- The second directional derivative in `HasPositiveTangentialHessianOn`, explicitly. -/
theorem fderiv_fderiv_apply_eq_kHess (μ c : ℝ) {s : Phase} (hs : s ∈ U) (u v : Phase) :
    fderiv ℝ (fun x => fderiv ℝ (leviCivitaHamiltonian μ c) x u) s v =
      ∑ k, ∑ l, u k * v l * kHess μ c s k l := by
  have hev : (fun x => fderiv ℝ (leviCivitaHamiltonian μ c) x u) =ᶠ[𝓝 s]
      fun x => u 0 * kGrad μ c x 0 + u 1 * kGrad μ c x 1 + u 2 * kGrad μ c x 2
        + u 3 * kGrad μ c x 3 := by
    filter_upwards [isOpen_U.mem_nhds hs] with x hx
    rw [fderiv_leviCivitaHamiltonian μ c hx, gradCLM_apply, dotProduct,
      Fin.sum_univ_four]
    ring
  have hg : HasGradAt (fun x => u 0 * kGrad μ c x 0 + u 1 * kGrad μ c x 1
      + u 2 * kGrad μ c x 2 + u 3 * kGrad μ c x 3) _ s :=
    ((((HasGradAt.const (u 0) s).mul (hasGradAt_kGrad μ c hs 0)).add
      ((HasGradAt.const (u 1) s).mul (hasGradAt_kGrad μ c hs 1))).add
      ((HasGradAt.const (u 2) s).mul (hasGradAt_kGrad μ c hs 2))).add
      ((HasGradAt.const (u 3) s).mul (hasGradAt_kGrad μ c hs 3))
  rw [hev.fderiv_eq, hg.fderiv_eq, gradCLM_apply]
  simp [dotProduct, Fin.sum_univ_four]
  ring

theorem continuousOn_kGrad (μ c : ℝ) : ContinuousOn (kGrad μ c) U :=
  continuousOn_pi.mpr fun k _ hs =>
    (hasGradAt_kGrad μ c hs k).differentiableAt.continuousAt.continuousWithinAt

theorem continuous_zNormSq : Continuous zNormSq := by unfold zNormSq; fun_prop

theorem continuous_hP (μ c : ℝ) (k l : Fin 4) : Continuous fun x => hP μ c x k l := by
  fin_cases k <;> fin_cases l <;> simp [hP] <;> fun_prop

theorem continuous_dZ (k : Fin 4) : Continuous fun x => dZ x k := by
  fin_cases k <;> simp [dZ] <;> fun_prop

theorem continuous_dD (k : Fin 4) : Continuous fun x => dD x k := by
  fin_cases k <;> simp [dD] <;> fun_prop

theorem continuous_hD (k l : Fin 4) : Continuous fun x => hD x k l := by
  fin_cases k <;> fin_cases l <;> simp [hD] <;> fun_prop

theorem continuousOn_kHess (μ c : ℝ) : ContinuousOn (kHess μ c) U := by
  refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => fun s hs => ?_
  have hr : rD s ≠ 0 := (rD_pos hs).ne'
  have := continuous_rD
  have := continuous_zNormSq
  have := continuous_hP μ c k l
  have := continuous_dZ k
  have := continuous_dZ l
  have := continuous_dD k
  have := continuous_dD l
  have := continuous_hD k l
  apply ContinuousAt.continuousWithinAt
  simp only [kHess, kHessR]
  fun_prop (disch := simp [hr])

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (μ c : ℝ) :
    (∀ s ∈ U, ∀ i : Fin 4,
      partialDerivative (leviCivitaHamiltonian μ c) s i = kGrad μ c s i) ∧
    (∀ s ∈ U, ∀ u v : Phase,
      fderiv ℝ (fun x => fderiv ℝ (leviCivitaHamiltonian μ c) x u) s v =
        ∑ k, ∑ l, u k * v l * kHess μ c s k l) ∧
    ContinuousOn (kGrad μ c) U ∧ ContinuousOn (kHess μ c) U := by
  exact ⟨fun s hs i => partialDerivative_eq_kGrad μ c hs i,
    fun s hs u v => fderiv_fderiv_apply_eq_kHess μ c hs u v,
    continuousOn_kGrad μ c, continuousOn_kHess μ c⟩
