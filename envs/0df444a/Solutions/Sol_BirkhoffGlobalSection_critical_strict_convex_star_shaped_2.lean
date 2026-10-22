-- Prove2me | solution 2 for BirkhoffGlobalSection.critical_strict_convex_star_shaped
-- status  : ACCEPTED   (disprove)
-- author  : @caleb
-- created : 2026-09-30T23:22:37.6888+00:00
-- url     : https://prove2.me/submissions/1d66db9f-8d20-4f28-87f6-06fedac66cfa

import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# `critical_strict_convex_star_shaped` is false: no regularization model exists at `(1/2, 2)`

At `μ = 1/2`, `c = 2` the energy is exactly critical. The Levi-Civita lift
`p₀ = (1/2, 0, 0, 0)` of the inner Lagrange point lies on the zero level, away from
the second collision, and the Levi-Civita gradient vanishes there. The path
`x ↦ (x, 0, √R(x), -(2x³ - x/2))` for `0 ≤ x ≤ 1/2` stays in the regular zero level
and joins the collision point to `p₀`, so `p₀` lies in the left energy component.

For any `M : RegularizationModel (1/2) 2`, the field `vectorField` at `p₀` gives
`0 = τ(p₀) • X_G(M p₀)` with `τ(p₀) > 0`, so every partial derivative of the model
Hamiltonian vanishes at `M p₀`. This contradicts `model_regular`. Hence the type
`RegularizationModel (1/2) 2` is empty, and the existence claim fails for every `U`,
for instance `U = univ`.

The gradient calculus is copied from the accepted proof of
`BirkhoffGlobalSection.TangentialHessian.leviCivita_explicit_derivatives`, because a
disproof may not import platform theorems.
-/

namespace BirkhoffGlobalSection.CriticalModelCounterexample

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

theorem fderiv_leviCivitaHamiltonian (μ c : ℝ) {s : Phase} (hs : s ∈ U) :
    fderiv ℝ (leviCivitaHamiltonian μ c) s = gradCLM (kGrad μ c s) :=
  (hasGradAt_leviCivitaHamiltonian μ c hs).fderiv_eq

theorem partialDerivative_eq_kGrad (μ c : ℝ) {s : Phase} (hs : s ∈ U) (i : Fin 4) :
    partialDerivative (leviCivitaHamiltonian μ c) s i = kGrad μ c s i := by
  simp [partialDerivative, fderiv_leviCivitaHamiltonian μ c hs, dotProduct,
    coordinateVector]


/-! ## The saddle-center lift is a critical point of the zero level -/

/-- The Levi-Civita lift `(1/2, 0, 0, 0)` of the inner Lagrange point for `μ = 1/2`. -/
def p₀ : Phase := ![1 / 2, 0, 0, 0]

theorem p₀_mem_U : p₀ ∈ U := by
  show 0 < secondCollisionDistanceSq p₀
  norm_num [secondCollisionDistanceSq, p₀]

theorem rD_p₀ : rD p₀ = 1 / 2 := by
  rw [rD, show secondCollisionDistanceSq p₀ = (1 / 2) ^ 2 by
    norm_num [secondCollisionDistanceSq, p₀]]
  exact Real.sqrt_sq (by norm_num)

theorem kGrad_p₀ : kGrad (1 / 2) 2 p₀ = 0 := by
  funext i
  simp only [kGrad, kGradR, rD_p₀]
  fin_cases i <;> simp [dP, dZ, dD, zNormSq, p₀] <;> norm_num

/-- The Levi-Civita field vanishes at `p₀`. -/
theorem hvf_p₀ : hamiltonianVectorField (leviCivitaHamiltonian (1 / 2) 2) p₀ = 0 := by
  have h : ∀ i, partialDerivative (leviCivitaHamiltonian (1 / 2) 2) p₀ i = 0 := by
    intro i
    rw [partialDerivative_eq_kGrad _ _ p₀_mem_U, kGrad_p₀]
    rfl
  unfold hamiltonianVectorField
  rw [h 0, h 1, h 2, h 3]
  funext i
  fin_cases i <;> simp

/-! ## `p₀` lies in the left energy component -/

/-- Squared momentum radius along the path. -/
def R2 (x : ℝ) : ℝ :=
  (1 - 4 * x ^ 2) ^ 2 * (2 + x ^ 2 - 2 * x ^ 4) / (4 * (1 - 2 * x ^ 2))

/-- A path in the regular zero level along the axis `z = (x, 0)`, from the collision
point at `x = 0` to the saddle-center lift at `x = 1/2`. -/
def path (x : ℝ) : Phase := ![x, 0, Real.sqrt (R2 x), -(2 * x ^ 3 - x / 2)]

theorem den_pos {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) : 0 < 1 - 2 * x ^ 2 := by
  obtain ⟨h0, h1⟩ := hx
  nlinarith

theorem R2_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) : 0 ≤ R2 x := by
  have hd := den_pos hx
  obtain ⟨h0, h1⟩ := hx
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hq : 0 < 2 + x ^ 2 - 2 * x ^ 4 := by nlinarith [sq_nonneg (x ^ 2)]
  unfold R2
  exact div_nonneg (mul_nonneg (sq_nonneg _) hq.le) (by linarith)

theorem continuousOn_path : ContinuousOn path (Set.Icc 0 (1 / 2)) := by
  have hR : ContinuousOn R2 (Set.Icc 0 (1 / 2)) := by
    unfold R2
    exact (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
      (fun x hx => (mul_pos (by norm_num : (0 : ℝ) < 4) (den_pos hx)).ne')
  apply continuousOn_pi.2
  intro i
  fin_cases i
  · exact continuousOn_id
  · exact continuousOn_const
  · exact hR.sqrt
  · exact (by fun_prop : Continuous fun x : ℝ => -(2 * x ^ 3 - x / 2)).continuousOn

theorem path_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    path x ∈ regularEnergyLocus (1 / 2) 2 := by
  have hd := den_pos hx
  have hd' : 1 - 2 * x ^ 2 ≠ 0 := hd.ne'
  have hR := Real.sq_sqrt (R2_nonneg hx)
  have hD : secondCollisionDistanceSq (path x) = (1 - 2 * x ^ 2) ^ 2 := by
    simp [secondCollisionDistanceSq, path]; ring
  refine ⟨?_, by rw [hD]; positivity⟩
  have hsD : Real.sqrt (secondCollisionDistanceSq (path x)) = 1 - 2 * x ^ 2 := by
    rw [hD]; exact Real.sqrt_sq hd.le
  simp only [leviCivitaHamiltonian]
  rw [hsD]
  simp [path, zNormSq, wNormSq, hR]
  have hinv : (1 - 2 * x ^ 2) * (1 - 2 * x ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hd'
  unfold R2
  field_simp
  linear_combination (8 - 60 * x ^ 2 - 32 * x ^ 4 + 64 * x ^ 6) * hinv

theorem path_zero : path 0 = leftCollisionPoint (1 / 2) := by
  have h : R2 0 = 1 - 1 / 2 := by norm_num [R2]
  unfold path leftCollisionPoint
  rw [h]
  funext i
  fin_cases i <;> simp

theorem path_half : path (1 / 2) = p₀ := by
  funext i
  fin_cases i <;> simp [path, p₀, R2] <;> norm_num

theorem p₀_mem : p₀ ∈ leftEnergyComponent (1 / 2) 2 := by
  have hpre : IsPreconnected (path '' Set.Icc 0 (1 / 2)) :=
    isPreconnected_Icc.image _ continuousOn_path
  have hsub : path '' Set.Icc 0 (1 / 2) ⊆ regularEnergyLocus (1 / 2) 2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact path_mem hx
  have h0 : leftCollisionPoint (1 / 2) ∈ path '' Set.Icc 0 (1 / 2) :=
    ⟨0, ⟨le_rfl, by norm_num⟩, path_zero⟩
  exact hpre.subset_connectedComponentIn h0 hsub ⟨1 / 2, ⟨by norm_num, le_rfl⟩, path_half⟩

/-! ## No regularization model exists at the critical level -/

/-- A continuous linear functional on `Phase` that vanishes on the coordinate vectors
is zero. -/
theorem fderiv_eq_zero_of_partials {G : Phase → ℝ} {y : Phase}
    (h : ∀ i, partialDerivative G y i = 0) : fderiv ℝ G y = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ i, v i • coordinateVector i := by
    funext j
    fin_cases j <;> simp [coordinateVector]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_eq_zero
  intro i _
  rw [show fderiv ℝ G y (coordinateVector i) = partialDerivative G y i from rfl, h i,
    smul_zero]

/-- The component contains a zero of the Levi-Civita field, where `vectorField` and
`model_regular` contradict each other. -/
theorem no_model (M : RegularizationModel (1 / 2) 2) : False := by
  have hv := M.vectorField p₀ p₀_mem
  rw [hvf_p₀, map_zero] at hv
  have hτ := M.timeScale_pos p₀ p₀_mem
  have hX : hamiltonianVectorField M.modelHamiltonian (M.toModel p₀) = 0 := by
    rcases smul_eq_zero.1 hv.symm with h | h
    · exact absurd h hτ.ne'
    · exact h
  apply M.model_regular p₀ p₀_mem
  apply fderiv_eq_zero_of_partials
  have h0 := congrFun hX 0
  have h1 := congrFun hX 1
  have h2 := congrFun hX 2
  have h3 := congrFun hX 3
  simp [hamiltonianVectorField] at h0 h1 h2 h3
  intro i
  fin_cases i
  · exact h2
  · exact h3
  · exact h0
  · exact h1

end

end BirkhoffGlobalSection.CriticalModelCounterexample

open BirkhoffGlobalSection BirkhoffGlobalSection.CriticalModelCounterexample

theorem solution : ¬ (∀ (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U),
    ∃ M₀ : RegularizationModel (1 / 2) 2,
      ∀ s ∈ leftEnergyComponent (1 / 2) 2, s ∉ U →
        IsStrictlyConvexStarShapedAt M₀.modelHamiltonian (M₀.toModel s)) := by
  intro h
  obtain ⟨M₀, -⟩ := h Set.univ isOpen_univ trivial trivial
  exact no_model M₀
