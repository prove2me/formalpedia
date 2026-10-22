-- Prove2me | solution 1 for BirkhoffGlobalSection.transported_winding_above_one
-- status  : ACCEPTED   (disprove)
-- author  : @caleb
-- created : 2026-09-29T22:57:52.142074+00:00
-- url     : https://prove2.me/submissions/52481c67-483e-4d19-9ba1-352bbecca066

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# `transported_winding_above_one` is false as stated

The statement assumes nothing about `x` beyond `y ∘ σ = M.toModel ∘ x`, and nothing
about `M` beyond the `RegularizationModel` fields, all of which only constrain the
left energy component. For `μ = 2` the canonical collision point is the origin, where
the Levi-Civita Hamiltonian equals `1/2`, so the component is empty. Then the identity
map with the zero model Hamiltonian is a regularization model; the zero Hamiltonian has
zero gradient, so its transverse frame vanishes and `hwind` holds vacuously.

For the conclusion we take `c = 4`, the constant curve at `p = (0,0,0,1)` and `T = 0`.
At `p` the Levi-Civita gradient is `(-2,0,0,1)` and `v = (1,0,0,2)` spans a kernel
direction of the Hessian, which is tangent to the level set with frame coordinates
`(0,-5)`. The linearized flow `exp (t • A)` fixes `v`, so the constant angle `-π/2`
is a valid polar angle, and its change over `[0, T] = [0, 0]` is `0 ≤ 2π`.

The gradient calculus below is copied from the accepted proof of
`BirkhoffGlobalSection.TangentialHessian.leviCivita_explicit_derivatives`, because a
disproof may not import platform theorems.
-/

namespace BirkhoffGlobalSection.TransportedWindingCounterexample

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

/-! ## The counterexample -/

/-- The base point `(z₁,z₂,w₁,w₂) = (0,0,0,1)`. -/
def p₀ : Phase := ![0, 0, 0, 1]

/-- A kernel vector of the Levi-Civita Hessian at `p₀` for `μ = 2, c = 4`. -/
def v₀ : Phase := ![1, 0, 0, 2]

theorem p₀_mem_U : p₀ ∈ U := by
  show 0 < secondCollisionDistanceSq p₀
  simp [secondCollisionDistanceSq, p₀]

theorem rD_p₀ : rD p₀ = 1 := by
  simp [rD, secondCollisionDistanceSq, p₀]

theorem kGrad_p₀ : kGrad 2 4 p₀ = ![-2, 0, 0, 1] := by
  funext i
  simp only [kGrad, kGradR, rD_p₀]
  fin_cases i <;> simp [dP, dZ, dD, zNormSq, p₀]

theorem grad_p₀ :
    TangentialHessian.grad (leviCivitaHamiltonian 2 4) p₀ = ![-2, 0, 0, 1] := by
  rw [← kGrad_p₀]
  funext i
  exact partialDerivative_eq_kGrad 2 4 p₀_mem_U i

/-- `v₀` is tangent to the level set through `p₀`. -/
theorem fderiv_p₀_v₀ : fderiv ℝ (leviCivitaHamiltonian 2 4) p₀ v₀ = 0 := by
  rw [fderiv_leviCivitaHamiltonian 2 4 p₀_mem_U, gradCLM_apply, kGrad_p₀]
  simp [v₀, dotProduct, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

/-- The frame coordinates of `v₀` at `p₀`. -/
theorem coords_p₀_v₀ :
    transverseFrameCoordinates (TangentialHessian.grad (leviCivitaHamiltonian 2 4) p₀) v₀ =
      ![0, -5] := by
  rw [grad_p₀]
  funext i
  fin_cases i <;>
    simp [transverseFrameCoordinates, frame, qJ, qK, v₀, dotProduct, Matrix.mulVec,
      Fin.sum_univ_four]
  all_goals norm_num

/-- `v₀` lies in the kernel of the explicit Hessian at `p₀`. -/
theorem kHess_p₀_v₀ (i : Fin 4) : ∑ l, kHess 2 4 p₀ i l * v₀ l = 0 := by
  simp only [kHess, kHessR, rD_p₀]
  fin_cases i <;> simp [Fin.sum_univ_four, hP, hZ, hD, dZ, dD, zNormSq, p₀, v₀]
  all_goals norm_num

theorem hasFDerivAt_partial (i : Fin 4) :
    HasFDerivAt (fun x => partialDerivative (leviCivitaHamiltonian 2 4) x i)
      (gradCLM (fun l => kHess 2 4 p₀ i l)) p₀ := by
  have hev : (fun x => partialDerivative (leviCivitaHamiltonian 2 4) x i) =ᶠ[𝓝 p₀]
      fun x => kGrad 2 4 x i := by
    filter_upwards [isOpen_U.mem_nhds p₀_mem_U] with x hx
    exact partialDerivative_eq_kGrad 2 4 hx i
  exact (hasGradAt_kGrad 2 4 p₀_mem_U i).hasFDerivAt.congr_of_eventuallyEq hev

theorem hasFDerivAt_vectorField :
    HasFDerivAt (hamiltonianVectorField (leviCivitaHamiltonian 2 4))
      (ContinuousLinearMap.pi ![gradCLM (fun l => kHess 2 4 p₀ 2 l),
        gradCLM (fun l => kHess 2 4 p₀ 3 l), -gradCLM (fun l => kHess 2 4 p₀ 0 l),
        -gradCLM (fun l => kHess 2 4 p₀ 1 l)]) p₀ := by
  have e : hamiltonianVectorField (leviCivitaHamiltonian 2 4) = fun x i =>
      (![fun x => partialDerivative (leviCivitaHamiltonian 2 4) x 2,
        fun x => partialDerivative (leviCivitaHamiltonian 2 4) x 3,
        fun x => -partialDerivative (leviCivitaHamiltonian 2 4) x 0,
        fun x => -partialDerivative (leviCivitaHamiltonian 2 4) x 1] :
          Fin 4 → Phase → ℝ) i x := by
    funext x i
    fin_cases i <;> rfl
  rw [e, hasFDerivAt_pi]
  intro i
  fin_cases i
  · exact hasFDerivAt_partial 2
  · exact hasFDerivAt_partial 3
  · exact (hasFDerivAt_partial 0).neg
  · exact (hasFDerivAt_partial 1).neg

/-- The linearized Levi-Civita field at `p₀`. -/
def A₀ : Phase →L[ℝ] Phase :=
  fderiv ℝ (hamiltonianVectorField (leviCivitaHamiltonian 2 4)) p₀

theorem A₀_v₀ : A₀ v₀ = 0 := by
  rw [A₀, hasFDerivAt_vectorField.fderiv]
  funext i
  rw [ContinuousLinearMap.pi_apply]
  have h := kHess_p₀_v₀
  fin_cases i
  · simpa [dotProduct] using h 2
  · simpa [dotProduct] using h 3
  · simp [dotProduct, h 0]
  · simp [dotProduct, h 1]

/-- The linearized flow along the constant curve at `p₀`. -/
def Y₀ (t : ℝ) : Phase →L[ℝ] Phase := NormedSpace.exp (t • A₀)

theorem Y₀_zero : Y₀ 0 = ContinuousLinearMap.id ℝ Phase := by
  rw [Y₀, zero_smul, NormedSpace.exp_zero]
  rfl

theorem hasDerivAt_Y₀ (t : ℝ) : HasDerivAt Y₀ (A₀.comp (Y₀ t)) t :=
  hasDerivAt_exp_smul_const' A₀ t

theorem Y₀_v₀ (t : ℝ) : Y₀ t v₀ = v₀ := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u => Y₀ u v₀) 0 s := by
    intro s
    have h := (hasDerivAt_exp_smul_const A₀ s).clm_apply (hasDerivAt_const s v₀)
    refine h.congr_deriv ?_
    show NormedSpace.exp (s • A₀) (A₀ v₀) + NormedSpace.exp (s • A₀) 0 = 0
    rw [A₀_v₀, map_zero, add_zero]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [Y₀_zero] using hconst

/-! ## The regularization model -/

theorem leftCollisionPoint_two : leftCollisionPoint 2 = 0 := by
  funext i
  fin_cases i <;> norm_num [leftCollisionPoint, Real.sqrt_eq_zero']

/-- For `μ = 2` the canonical collision point is off the zero level, so the component
is empty. -/
theorem leftEnergyComponent_two (c : ℝ) : leftEnergyComponent 2 c = ∅ := by
  apply connectedComponentIn_eq_empty
  intro h
  have h0 := h.1
  rw [leftCollisionPoint_two] at h0
  norm_num [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq] at h0

/-- The identity regularization model with zero model Hamiltonian, valid because the
component is empty. -/
def trivialModel (c : ℝ) : RegularizationModel 2 c where
  source := Set.univ
  target := Set.univ
  source_open := isOpen_univ
  target_open := isOpen_univ
  contains_component := Set.subset_univ _
  toModel := id
  fromModel := id
  toModel_mapsTo := Set.mapsTo_univ _ _
  fromModel_mapsTo := Set.mapsTo_univ _ _
  left_inverse := fun _ _ => rfl
  right_inverse := fun _ _ => rfl
  toModel_smooth := contDiffOn_id
  fromModel_smooth := contDiffOn_id
  symplecticScale := 1
  symplecticScale_pos := one_pos
  symplectic := fun s _ v w => by simp
  antipodal := fun _ _ => rfl
  modelHamiltonian := fun _ => 0
  model_smooth := contDiffOn_const
  model_zero := fun _ _ => rfl
  model_regular := fun s hs => by
    rw [leftEnergyComponent_two] at hs
    exact hs.elim
  timeScale := fun _ => 1
  timeScale_continuous := continuousOn_const
  timeScale_pos := fun _ _ => one_pos
  vectorField := fun s hs => by
    rw [leftEnergyComponent_two] at hs
    exact hs.elim

theorem grad_zero (s : Phase) :
    TangentialHessian.grad (fun _ : Phase => (0 : ℝ)) s = 0 := by
  funext i
  simp [TangentialHessian.grad, partialDerivative]

/-- The zero Hamiltonian has vanishing transverse frame, so the winding condition is
vacuous. -/
theorem zero_model_winding (y : ℝ → Phase) (T : ℝ) :
    HasTransverseWindingAboveOne (fun _ : Phase => (0 : ℝ)) y T := by
  intro Y _ _ v _ hv
  exfalso
  apply hv
  rw [grad_zero]
  funext i
  fin_cases i <;> simp [transverseFrameCoordinates, frame]

end

end BirkhoffGlobalSection.TransportedWindingCounterexample

open BirkhoffGlobalSection BirkhoffGlobalSection.TransportedWindingCounterexample

theorem solution : ¬ (∀ (μ c : ℝ) (M : RegularizationModel μ c) (S : Set Phase)
    (x : ℝ → Phase) (T : ℝ)
    (y : ℝ → Phase) (T' : ℝ) (σ : ℝ → ℝ)
    (hσ : StrictMono σ) (hσ0 : σ 0 = 0) (hσT : σ T = T')
    (hrel : ∀ t : ℝ, y (σ t) = M.toModel (x t))
    (hwind : HasTransverseWindingAboveOne M.modelHamiltonian y T'),
    HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T) := by
  intro h
  have hw := h 2 4 (trivialModel 4) ∅ (fun _ => p₀) 0 (fun _ => p₀) 0 id strictMono_id
    rfl rfl (fun _ => rfl) (zero_model_winding _ _)
  have hcoord : transverseFrameCoordinates
      (TangentialHessian.grad (leviCivitaHamiltonian 2 4) p₀) v₀ ≠ 0 := by
    rw [coords_p₀_v₀]
    intro h0
    have := congrFun h0 1
    norm_num at this
  have hrep : ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      transverseFrameCoordinates (TangentialHessian.grad (leviCivitaHamiltonian 2 4) p₀)
        (Y₀ t v₀) = ![ρ * Real.cos (-(Real.pi / 2)), ρ * Real.sin (-(Real.pi / 2))] := by
    intro t
    refine ⟨5, by norm_num, ?_⟩
    rw [Y₀_v₀, coords_p₀_v₀]
    funext i
    fin_cases i <;> simp [Real.cos_neg, Real.sin_neg]
  have hlt := hw Y₀ Y₀_zero hasDerivAt_Y₀ v₀ fderiv_p₀_v₀ hcoord
    (fun _ => -(Real.pi / 2)) continuous_const hrep
  rw [sub_self] at hlt
  linarith [Real.pi_pos]
