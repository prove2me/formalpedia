-- Prove2me | solution 1 for BirkhoffGlobalSection.transported_closed_winding_above_one
-- status  : ACCEPTED   (disprove)
-- author  : @caleb
-- created : 2026-09-30T20:47:36.472572+00:00
-- url     : https://prove2.me/submissions/3faf6b24-4317-42fb-8c26-774d902c7ddc

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# `transported_closed_winding_above_one` is false as stated

The clock hypothesis `hσ` asks only that `σ` be strictly monotone, not continuous. A
strictly monotone clock may jump over whole periods, and then `y` is a multiple cover of
the transported orbit. So `hwind` constrains the multiple cover, not the orbit itself.

Take `μ = 0` and `c = -15/8`. The collision term vanishes, so the Levi-Civita
Hamiltonian `K₀` is a polynomial. Use the identity regularization model and `S = univ`.
The circular orbit `z = (1+i) e^{9it/2}`, `w = i z / 2` lies in the left energy
component; an explicit path in the regular zero level joins it to the collision point.
Its period is `T₀ = 4π/9`.

Along the orbit, the frame coordinates `ξ` of any tangent solution of the variational
equation satisfy `ξ₁' = -(4/5) ξ₂ + (37/5) γ` and `ξ₂' = (5/4) ξ₁`, where the
gradient pairing `γ` is constant zero. So every continuous polar angle advances by the
elapsed time up to an error below `π`. Over seven periods the angle gains more than
`28π/9 - π > 2π`. Over one period it gains less than `4π/9 + π/2 < 2π`.

The clock `σ t = t` for `t < T₀` and `σ t = t + 6 T₀` otherwise makes `y = x` the
seven-fold cover, so every hypothesis holds while the conclusion fails.

The gradient calculus is copied from the accepted proof of
`BirkhoffGlobalSection.TangentialHessian.leviCivita_explicit_derivatives`, because a
disproof may not import platform theorems.
-/

namespace BirkhoffGlobalSection.ClosedWindingCounterexample

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

theorem hasFDerivAt (hf : HasGradAt f g s) : HasFDerivAt f (gradCLM g) s := hf

theorem fderiv_eq (hf : HasGradAt f g s) : fderiv ℝ f s = gradCLM g :=
  hf.hasFDerivAt.fderiv

end HasGradAt

theorem hasGradAt_pP (μ c : ℝ) (s : Phase) : HasGradAt (pP μ c) (dP μ c s) s := by
  show HasGradAt (fun x => (x 2 ^ 2 + x 3 ^ 2) / 2 + c * (x 0 ^ 2 + x 1 ^ 2) - (1 - μ) / 2
    + 2 * (x 0 ^ 2 + x 1 ^ 2) * (x 0 * x 3 - x 1 * x 2) - μ * (x 0 * x 3 + x 1 * x 2)) _ s
  apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.pow, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
  funext l; fin_cases l <;> simp [dP] <;> ring

theorem hasGradAt_dP (μ c : ℝ) (s : Phase) (k : Fin 4) :
    HasGradAt (fun x => dP μ c x k) (fun l => hP μ c s k l) s := by
  fin_cases k
  · show HasGradAt (fun x => 2 * c * x 0 - μ * x 3 - 4 * x 2 * x 0 * x 1
      + 6 * x 3 * x 0 ^ 2 + 2 * x 3 * x 1 ^ 2) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.pow, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hP] <;> ring
  · show HasGradAt (fun x => 2 * c * x 1 - μ * x 2 - 2 * x 2 * x 0 ^ 2
      - 6 * x 2 * x 1 ^ 2 + 4 * x 3 * x 0 * x 1) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.pow, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hP] <;> ring
  · show HasGradAt (fun x => -μ * x 1 + x 2 - 2 * x 0 ^ 2 * x 1 - 2 * x 1 ^ 3) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.pow, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hP] <;> ring
  · show HasGradAt (fun x => -μ * x 0 + x 3 + 2 * x 0 ^ 3 + 2 * x 0 * x 1 ^ 2) _ s
    apply HasGradAt.congr_grad (by apply_rules (maxDepth := 400) [HasGradAt.const, HasGradAt.coord, HasGradAt.pow, HasGradAt.sub, HasGradAt.neg, HasGradAt.add, HasGradAt.mul])
    funext l; fin_cases l <;> simp [hP] <;> ring

/-! ## The Levi-Civita Hamiltonian for `μ = 0`, `c = -15/8` -/

/-- The energy parameter of the counterexample. -/
def c₀ : ℝ := -15 / 8

/-- The Levi-Civita Hamiltonian with `μ = 0`. The collision term drops out. -/
abbrev K₀ : Phase → ℝ := leviCivitaHamiltonian 0 c₀

theorem K₀_eq : K₀ = pP 0 c₀ := by
  funext s; unfold K₀ leviCivitaHamiltonian pP; ring

theorem fderiv_K₀ (s : Phase) : fderiv ℝ K₀ s = gradCLM (dP 0 c₀ s) := by
  rw [K₀_eq]; exact (hasGradAt_pP 0 c₀ s).fderiv_eq

theorem partial_K₀ (s : Phase) (i : Fin 4) :
    partialDerivative K₀ s i = dP 0 c₀ s i := by
  simp [partialDerivative, fderiv_K₀, dotProduct, coordinateVector]

theorem grad_K₀ (s : Phase) : TangentialHessian.grad K₀ s = dP 0 c₀ s := by
  funext i; exact partial_K₀ s i

theorem hvf_eq : hamiltonianVectorField K₀ = fun x i =>
    (![fun x => dP 0 c₀ x 2, fun x => dP 0 c₀ x 3, fun x => -dP 0 c₀ x 0,
      fun x => -dP 0 c₀ x 1] : Fin 4 → Phase → ℝ) i x := by
  funext x i
  fin_cases i <;> simp [hamiltonianVectorField, partial_K₀]

/-- The linearized Hamiltonian vector field. -/
def DX (p : Phase) : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![gradCLM (fun l => hP 0 c₀ p 2 l),
    gradCLM (fun l => hP 0 c₀ p 3 l), -gradCLM (fun l => hP 0 c₀ p 0 l),
    -gradCLM (fun l => hP 0 c₀ p 1 l)]

theorem hasFDerivAt_X (p : Phase) :
    HasFDerivAt (hamiltonianVectorField K₀) (DX p) p := by
  rw [hvf_eq, DX, hasFDerivAt_pi]
  intro i
  fin_cases i
  · exact (hasGradAt_dP 0 c₀ p 2).hasFDerivAt
  · exact (hasGradAt_dP 0 c₀ p 3).hasFDerivAt
  · exact (hasGradAt_dP 0 c₀ p 0).hasFDerivAt.neg
  · exact (hasGradAt_dP 0 c₀ p 1).hasFDerivAt.neg

theorem fderiv_X (p : Phase) : fderiv ℝ (hamiltonianVectorField K₀) p = DX p :=
  (hasFDerivAt_X p).fderiv

theorem DX_apply (p w : Phase) (i : Fin 4) :
    DX p w i = (![∑ l, hP 0 c₀ p 2 l * w l, ∑ l, hP 0 c₀ p 3 l * w l,
      -∑ l, hP 0 c₀ p 0 l * w l, -∑ l, hP 0 c₀ p 1 l * w l] : Phase) i := by
  fin_cases i <;> simp [DX, dotProduct]

/-! ## The circular orbit -/

def Cf (t : ℝ) : ℝ := Real.cos (9 / 2 * t)

def Sf (t : ℝ) : ℝ := Real.sin (9 / 2 * t)

theorem CS_one (t : ℝ) : Cf t ^ 2 + Sf t ^ 2 = 1 := by
  simp only [Cf, Sf]; exact Real.cos_sq_add_sin_sq _

theorem hasDerivAt_Cf (t : ℝ) : HasDerivAt Cf (-(9 / 2) * Sf t) t := by
  have h := (Real.hasDerivAt_cos (9 / 2 * t)).comp t
    ((hasDerivAt_id t).const_mul (9 / 2 : ℝ))
  refine h.congr_deriv ?_
  simp [Sf]; ring

theorem hasDerivAt_Sf (t : ℝ) : HasDerivAt Sf (9 / 2 * Cf t) t := by
  have h := (Real.hasDerivAt_sin (9 / 2 * t)).comp t
    ((hasDerivAt_id t).const_mul (9 / 2 : ℝ))
  refine h.congr_deriv ?_
  simp [Cf]; ring

theorem continuous_Cf : Continuous Cf := by unfold Cf; fun_prop

theorem continuous_Sf : Continuous Sf := by unfold Sf; fun_prop

/-- The circular Levi-Civita orbit through `(z, w) = ((1,1), (-1/2, 1/2))`. -/
def orbit (t : ℝ) : Phase :=
  ![Cf t - Sf t, Sf t + Cf t, -(Cf t + Sf t) / 2, (Cf t - Sf t) / 2]

@[simp] theorem orbit_0 (t : ℝ) : orbit t 0 = Cf t - Sf t := rfl
@[simp] theorem orbit_1 (t : ℝ) : orbit t 1 = Sf t + Cf t := rfl
@[simp] theorem orbit_2 (t : ℝ) : orbit t 2 = -(Cf t + Sf t) / 2 := rfl
@[simp] theorem orbit_3 (t : ℝ) : orbit t 3 = (Cf t - Sf t) / 2 := rfl

theorem continuous_orbit : Continuous orbit := by
  have hC := continuous_Cf
  have hS := continuous_Sf
  apply continuous_pi
  intro i
  fin_cases i
  · exact hC.sub hS
  · exact hS.add hC
  · exact (hC.add hS).neg.div_const 2
  · exact (hC.sub hS).div_const 2

theorem hasDerivAt_orbit (t : ℝ) :
    HasDerivAt orbit (hamiltonianVectorField K₀ (orbit t)) t := by
  have hC := hasDerivAt_Cf t
  have hS := hasDerivAt_Sf t
  have e := CS_one t
  rw [hasDerivAt_pi]
  intro i
  rw [hvf_eq]
  fin_cases i
  · refine (hC.sub hS).congr_deriv ?_
    simp [dP, c₀]
    linear_combination (4 * (Cf t + Sf t)) * e
  · refine (hS.add hC).congr_deriv ?_
    simp [dP, c₀]
    linear_combination (-4 * (Cf t - Sf t)) * e
  · refine ((hC.add hS).neg.div_const 2).congr_deriv ?_
    simp [dP, c₀]
    linear_combination (6 * (Cf t - Sf t)) * e
  · refine ((hC.sub hS).div_const 2).congr_deriv ?_
    simp [dP, c₀]
    linear_combination (6 * (Cf t + Sf t)) * e

theorem K₀_orbit (t : ℝ) : K₀ (orbit t) = 0 := by
  rw [K₀_eq]
  simp [pP, c₀, zNormSq, wNormSq]
  linear_combination (4 * Cf t ^ 2 + 4 * Sf t ^ 2 + 1 / 2) * CS_one t

theorem D_orbit_pos (t : ℝ) : 0 < secondCollisionDistanceSq (orbit t) := by
  have e := CS_one t
  have h : secondCollisionDistanceSq (orbit t) = 17 + 16 * Cf t * Sf t := by
    simp [secondCollisionDistanceSq]
    linear_combination (16 * Cf t ^ 2 + 16 * Sf t ^ 2 + 16) * e
  rw [h]
  nlinarith [sq_nonneg (Cf t + Sf t)]

/-- The gradient along the orbit. -/
def gO (t : ℝ) : Phase :=
  ![9 / 4 * (Cf t - Sf t), 9 / 4 * (Cf t + Sf t), -(9 / 2) * (Cf t + Sf t),
    9 / 2 * (Cf t - Sf t)]

theorem dP_orbit (t : ℝ) : dP 0 c₀ (orbit t) = gO t := by
  have e := CS_one t
  funext i
  fin_cases i <;> simp [dP, gO, c₀]
  · linear_combination (6 * Cf t - 6 * Sf t) * e
  · linear_combination (6 * Cf t + 6 * Sf t) * e
  · linear_combination (-4 * Cf t - 4 * Sf t) * e
  · linear_combination (4 * Cf t - 4 * Sf t) * e

theorem orbit_zero : orbit 0 = ![1, 1, -1 / 2, 1 / 2] := by
  funext i; fin_cases i <;> simp [orbit, Cf, Sf]

/-- The half period `T₀ = 4π/9` of `9t/2`. -/
def T₀ : ℝ := 4 * Real.pi / 9

theorem T₀_pos : 0 < T₀ := by unfold T₀; positivity

theorem orbit_add_period (t : ℝ) (n : ℕ) : orbit (t + n * T₀) = orbit t := by
  have hC : Cf (t + n * T₀) = Cf t := by
    simp only [Cf, T₀]
    rw [show 9 / 2 * (t + n * (4 * Real.pi / 9)) = 9 / 2 * t + (n : ℤ) * (2 * Real.pi) by
      push_cast; ring]
    exact Real.cos_add_int_mul_two_pi _ _
  have hS : Sf (t + n * T₀) = Sf t := by
    simp only [Sf, T₀]
    rw [show 9 / 2 * (t + n * (4 * Real.pi / 9)) = 9 / 2 * t + (n : ℤ) * (2 * Real.pi) by
      push_cast; ring]
    exact Real.sin_add_int_mul_two_pi _ _
  simp only [orbit, hC, hS]

/-! ## The orbit lies in the left energy component -/

def pd (l : ℝ) : ℝ := (1 - 2 * l) ^ 2 + l ^ 2

def pQ (l : ℝ) : ℝ := 32 * l ^ 6 + 15 / 2 * l ^ 2 + 1

def pk (l : ℝ) : ℝ := Real.sqrt (pQ l / pd l)

theorem pd_pos (l : ℝ) : 0 < pd l := by
  unfold pd; nlinarith [sq_nonneg (5 * l - 2)]

theorem pk_sq (l : ℝ) : pk l ^ 2 * pd l = pQ l := by
  have hd := pd_pos l
  have hQ : 0 ≤ pQ l / pd l := div_nonneg (by unfold pQ; positivity) hd.le
  rw [pk, Real.sq_sqrt hQ, div_mul_cancel₀ _ hd.ne']

theorem continuous_pk : Continuous pk := by
  unfold pk
  exact ((by unfold pQ; fun_prop : Continuous pQ).div (by unfold pd; fun_prop)
    (fun l => (pd_pos l).ne')).sqrt

/-- A path in the regular zero level from the collision point to `orbit 0`: the base
point moves along the diagonal `z = (l, l)` and the momentum stays on the fibre circle. -/
def path (l : ℝ) : Phase :=
  ![l, l, 4 * l ^ 3 + pk l * (1 - 2 * l), -4 * l ^ 3 + pk l * l]

theorem continuous_path : Continuous path := by
  have hk := continuous_pk
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_id
  · exact continuous_id
  · show Continuous fun l => 4 * l ^ 3 + pk l * (1 - 2 * l)
    fun_prop
  · show Continuous fun l => -4 * l ^ 3 + pk l * l
    fun_prop

theorem path_mem (l : ℝ) : path l ∈ regularEnergyLocus 0 c₀ := by
  constructor
  · show K₀ (path l) = 0
    rw [K₀_eq]
    have h := pk_sq l
    unfold pd pQ at h
    simp [pP, path, c₀, zNormSq, wNormSq]
    linear_combination (1 / 2) * h
  · have e : secondCollisionDistanceSq (path l) = 1 + 16 * l ^ 4 := by
      simp [secondCollisionDistanceSq, path]; ring
    rw [e]; positivity

theorem path_zero : path 0 = leftCollisionPoint 0 := by
  have h : pk 0 = 1 := by simp [pk, pQ, pd]
  funext i; fin_cases i <;> simp [path, leftCollisionPoint, h]

theorem path_one : path 1 = orbit 0 := by
  have h : pk 1 = 9 / 2 := by
    rw [pk, show pQ 1 / pd 1 = (9 / 2) ^ 2 by norm_num [pQ, pd]]
    exact Real.sqrt_sq (by norm_num)
  rw [orbit_zero]; funext i; fin_cases i <;> simp [path, h] <;> norm_num

theorem orbit_zero_mem : orbit 0 ∈ leftEnergyComponent 0 c₀ := by
  have hpre : IsPreconnected (path '' Set.Icc 0 1) :=
    isPreconnected_Icc.image _ continuous_path.continuousOn
  have hsub : path '' Set.Icc 0 1 ⊆ regularEnergyLocus 0 c₀ := by
    rintro _ ⟨l, -, rfl⟩; exact path_mem l
  have h0 : leftCollisionPoint 0 ∈ path '' Set.Icc 0 1 :=
    ⟨0, ⟨le_rfl, zero_le_one⟩, path_zero⟩
  exact hpre.subset_connectedComponentIn h0 hsub ⟨1, ⟨zero_le_one, le_rfl⟩, path_one⟩

theorem orbit_mem (t : ℝ) : orbit t ∈ leftEnergyComponent 0 c₀ := by
  have hpre : IsPreconnected (Set.range orbit) := isPreconnected_range continuous_orbit
  have hsub : Set.range orbit ⊆ regularEnergyLocus 0 c₀ := by
    rintro _ ⟨s, rfl⟩; exact ⟨K₀_orbit s, D_orbit_pos s⟩
  have h := hpre.subset_connectedComponentIn ⟨0, rfl⟩ hsub ⟨t, rfl⟩
  unfold leftEnergyComponent
  rw [connectedComponentIn_eq orbit_zero_mem]
  exact h

/-! ## The identity regularization model -/

theorem K₀_identity (s : Phase) : K₀ s = ((dP 0 c₀ s 2) ^ 2 + (dP 0 c₀ s 3) ^ 2) / 2
    - 2 * (s 0 ^ 2 + s 1 ^ 2) ^ 3 - 15 / 8 * (s 0 ^ 2 + s 1 ^ 2) - 1 / 2 := by
  rw [K₀_eq]; simp [pP, dP, c₀, zNormSq, wNormSq]; ring

/-- On the zero level of `K₀`, the momentum gradient `∂K/∂w` never vanishes. -/
theorem fderiv_K₀_ne (s : Phase) (hs : K₀ s = 0) : fderiv ℝ K₀ s ≠ 0 := by
  intro h
  have h2 : dP 0 c₀ s 2 = 0 := by rw [← partial_K₀]; simp [partialDerivative, h]
  have h3 : dP 0 c₀ s 3 = 0 := by rw [← partial_K₀]; simp [partialDerivative, h]
  have hid := K₀_identity s
  rw [hs, h2, h3] at hid
  nlinarith [sq_nonneg (s 0), sq_nonneg (s 1),
    pow_nonneg (add_nonneg (sq_nonneg (s 0)) (sq_nonneg (s 1))) 3]

/-- The identity map is a regularization model for `μ = 0`, `c = -15/8`, with model
Hamiltonian `K₀` itself and unit time scale. -/
def idModel : RegularizationModel 0 c₀ where
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
  modelHamiltonian := K₀
  model_smooth := by
    rw [K₀_eq]; unfold pP zNormSq wNormSq; apply ContDiff.contDiffOn; fun_prop
  model_zero := fun _ hs => (connectedComponentIn_subset _ _ hs).1
  model_regular := fun s hs => fderiv_K₀_ne s (connectedComponentIn_subset _ _ hs).1
  timeScale := fun _ => 1
  timeScale_continuous := continuousOn_const
  timeScale_pos := fun _ _ => one_pos
  vectorField := fun s _ => by simp

/-! ## The linearized flow in frame coordinates -/

/-- First frame coordinate of a vector field `u` along the orbit. -/
def ξ1 (u : ℝ → Phase) (t : ℝ) : ℝ :=
  u t 0 * (9 / 4 * (Cf t + Sf t)) + u t 1 * (9 / 4 * (Sf t - Cf t))
    + u t 2 * (9 / 2 * (Sf t - Cf t)) + u t 3 * (-(9 / 2) * (Cf t + Sf t))

/-- Second frame coordinate of a vector field `u` along the orbit. -/
def ξ2 (u : ℝ → Phase) (t : ℝ) : ℝ :=
  u t 0 * (9 / 2 * (Sf t - Cf t)) + u t 1 * (-(9 / 2) * (Cf t + Sf t))
    + u t 2 * (-(9 / 4) * (Cf t + Sf t)) + u t 3 * (9 / 4 * (Cf t - Sf t))

/-- The pairing of `u` with the gradient along the orbit. -/
def γ (u : ℝ → Phase) (t : ℝ) : ℝ :=
  u t 0 * (9 / 4 * (Cf t - Sf t)) + u t 1 * (9 / 4 * (Cf t + Sf t))
    + u t 2 * (-(9 / 2) * (Cf t + Sf t)) + u t 3 * (9 / 2 * (Cf t - Sf t))

theorem tfc_orbit (u : ℝ → Phase) (t : ℝ) :
    transverseFrameCoordinates (TangentialHessian.grad K₀ (orbit t)) (u t) =
      ![ξ1 u t, ξ2 u t] := by
  rw [grad_K₀, dP_orbit]
  funext i
  fin_cases i <;>
    simp [transverseFrameCoordinates, frame, qJ, qK, gO, dotProduct, Matrix.mulVec,
      Fin.sum_univ_four, ξ1, ξ2] <;> ring

section Lin

variable (u : ℝ → Phase) (hu : ∀ t, HasDerivAt u (DX (orbit t) (u t)) t)
include hu

theorem hasDerivAt_ξ1 (t : ℝ) :
    HasDerivAt (ξ1 u) (-(4 / 5) * ξ2 u t + 37 / 5 * γ u t) t := by
  have hC := hasDerivAt_Cf t
  have hS := hasDerivAt_Sf t
  have h0 := hasDerivAt_pi.1 (hu t) 0
  have h1 := hasDerivAt_pi.1 (hu t) 1
  have h2 := hasDerivAt_pi.1 (hu t) 2
  have h3 := hasDerivAt_pi.1 (hu t) 3
  have h := (((h0.mul ((hC.add hS).const_mul (9 / 4))).add
    (h1.mul ((hS.sub hC).const_mul (9 / 4)))).add
    (h2.mul ((hS.sub hC).const_mul (9 / 2)))).add
    (h3.mul ((hC.add hS).const_mul (-(9 / 2))))
  refine h.congr_deriv ?_
  simp only [DX_apply]
  simp [hP, c₀, Fin.sum_univ_four, ξ2, γ]
  linear_combination (27 * (Cf t * u t 0 + Cf t * u t 1 - 2 * Cf t * u t 2
    + 2 * Cf t * u t 3 - Sf t * u t 0 + Sf t * u t 1 - 2 * Sf t * u t 2
    - 2 * Sf t * u t 3)) * CS_one t

theorem hasDerivAt_ξ2 (t : ℝ) : HasDerivAt (ξ2 u) (5 / 4 * ξ1 u t) t := by
  have hC := hasDerivAt_Cf t
  have hS := hasDerivAt_Sf t
  have h0 := hasDerivAt_pi.1 (hu t) 0
  have h1 := hasDerivAt_pi.1 (hu t) 1
  have h2 := hasDerivAt_pi.1 (hu t) 2
  have h3 := hasDerivAt_pi.1 (hu t) 3
  have h := (((h0.mul ((hS.sub hC).const_mul (9 / 2))).add
    (h1.mul ((hC.add hS).const_mul (-(9 / 2))))).add
    (h2.mul ((hC.add hS).const_mul (-(9 / 4))))).add
    (h3.mul ((hC.sub hS).const_mul (9 / 4)))
  refine h.congr_deriv ?_
  simp only [DX_apply]
  simp [hP, c₀, Fin.sum_univ_four, ξ1]
  linear_combination (-9 * (Cf t * u t 0 - Cf t * u t 1 - Cf t * u t 2 - Cf t * u t 3
    + Sf t * u t 0 + Sf t * u t 1 + Sf t * u t 2 - Sf t * u t 3)) * CS_one t

theorem hasDerivAt_γ (t : ℝ) : HasDerivAt (γ u) 0 t := by
  have hC := hasDerivAt_Cf t
  have hS := hasDerivAt_Sf t
  have h0 := hasDerivAt_pi.1 (hu t) 0
  have h1 := hasDerivAt_pi.1 (hu t) 1
  have h2 := hasDerivAt_pi.1 (hu t) 2
  have h3 := hasDerivAt_pi.1 (hu t) 3
  have h := (((h0.mul ((hC.sub hS).const_mul (9 / 4))).add
    (h1.mul ((hC.add hS).const_mul (9 / 4)))).add
    (h2.mul ((hC.add hS).const_mul (-(9 / 2))))).add
    (h3.mul ((hC.sub hS).const_mul (9 / 2)))
  refine h.congr_deriv ?_
  simp only [DX_apply]
  simp [hP, c₀, Fin.sum_univ_four]
  linear_combination (9 * (3 * Cf t * u t 0 - 3 * Cf t * u t 1 + 2 * Cf t * u t 2
    + 2 * Cf t * u t 3 + 3 * Sf t * u t 0 + 3 * Sf t * u t 1 - 2 * Sf t * u t 2
    + 2 * Sf t * u t 3)) * CS_one t

/-- If `u` starts tangent to the level set, its frame coordinates rotate as the
linear system `ξ₁' = -(4/5) ξ₂`, `ξ₂' = (5/4) ξ₁`. -/
theorem ξ_formula (hγ0 : γ u 0 = 0) (t : ℝ) :
    ξ1 u t = ξ1 u 0 * Real.cos t - 4 / 5 * ξ2 u 0 * Real.sin t ∧
      ξ2 u t = 5 / 4 * ξ1 u 0 * Real.sin t + ξ2 u 0 * Real.cos t := by
  have hγ : ∀ s, γ u s = 0 := by
    intro s
    have hc := is_const_of_deriv_eq_zero (fun x => (hasDerivAt_γ u hu x).differentiableAt)
      (fun x => (hasDerivAt_γ u hu x).deriv) s 0
    rw [hc, hγ0]
  have h1 : ∀ s, HasDerivAt (ξ1 u) (-(4 / 5) * ξ2 u s) s := fun s =>
    (hasDerivAt_ξ1 u hu s).congr_deriv (by rw [hγ s]; ring)
  have h2 := hasDerivAt_ξ2 u hu
  have hP : ∀ s, HasDerivAt (fun y => 5 * ξ1 u y * Real.cos y + 4 * ξ2 u y * Real.sin y)
      0 s := by
    intro s
    refine ((((h1 s).const_mul 5).mul (Real.hasDerivAt_cos s)).add
      (((h2 s).const_mul 4).mul (Real.hasDerivAt_sin s))).congr_deriv ?_
    ring
  have hQ : ∀ s, HasDerivAt (fun y => -5 * ξ1 u y * Real.sin y + 4 * ξ2 u y * Real.cos y)
      0 s := by
    intro s
    refine ((((h1 s).const_mul (-5)).mul (Real.hasDerivAt_sin s)).add
      (((h2 s).const_mul 4).mul (Real.hasDerivAt_cos s))).congr_deriv ?_
    ring
  have cP := is_const_of_deriv_eq_zero (fun x => (hP x).differentiableAt)
    (fun x => (hP x).deriv) t 0
  have cQ := is_const_of_deriv_eq_zero (fun x => (hQ x).differentiableAt)
    (fun x => (hQ x).deriv) t 0
  simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero, zero_add] at cP cQ
  have hcs := Real.cos_sq_add_sin_sq t
  constructor
  · linear_combination (Real.cos t / 5) * cP - (Real.sin t / 5) * cQ - ξ1 u t * hcs
  · linear_combination (Real.sin t / 4) * cP + (Real.cos t / 4) * cQ - ξ2 u t * hcs

end Lin

/-- Frame coordinates of the linearized flow along the orbit, for any solution of the
variational equation and any initial vector tangent to the level set. -/
theorem core (Y : ℝ → Phase →L[ℝ] Phase) (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField K₀) (orbit t)).comp (Y t)) t)
    (v : Phase) (hv : fderiv ℝ K₀ (orbit 0) v = 0) (t : ℝ) :
    transverseFrameCoordinates (TangentialHessian.grad K₀ (orbit t)) (Y t v) =
      ![ξ1 (fun s => Y s v) 0 * Real.cos t - 4 / 5 * ξ2 (fun s => Y s v) 0 * Real.sin t,
        5 / 4 * ξ1 (fun s => Y s v) 0 * Real.sin t
          + ξ2 (fun s => Y s v) 0 * Real.cos t] := by
  set u : ℝ → Phase := fun s => Y s v with hu_def
  have hu : ∀ s, HasDerivAt u (DX (orbit s) (u s)) s := by
    intro s
    have h := (hY s).clm_apply (hasDerivAt_const s v)
    rw [fderiv_X] at h
    refine h.congr_deriv ?_
    simp [u]
  have hγ0 : γ u 0 = 0 := by
    have hv' := hv
    rw [fderiv_K₀, gradCLM_apply, dP_orbit] at hv'
    have hu0 : u 0 = v := by simp [u, hY0]
    simp only [γ, hu0]
    simp [gO, dotProduct, Fin.sum_univ_four, Cf, Sf] at hv' ⊢
    linarith
  obtain ⟨e1, e2⟩ := ξ_formula u hu hγ0 t
  have h := tfc_orbit u t
  simp only [u] at h
  rw [h, e1, e2]

/-! ## Angle lifts -/

theorem const_of_two_pi_int {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b))
    (hint : ∀ t ∈ Set.Icc a b, ∃ k : ℤ, g t = k * (2 * Real.pi)) :
    g b = g a := by
  obtain ⟨k₁, hk₁⟩ := hint a ⟨le_rfl, hab⟩
  obtain ⟨k₂, hk₂⟩ := hint b ⟨hab, le_rfl⟩
  have hπ := Real.pi_pos
  have hodd : ∀ m n : ℤ, (m : ℝ) * (2 * Real.pi) ≠ n * (2 * Real.pi) + Real.pi := by
    intro m n h
    have h' : ((2 * (m - n) : ℤ) : ℝ) * Real.pi = 1 * Real.pi := by
      push_cast; linarith
    have h'' : ((2 * (m - n) : ℤ) : ℝ) = 1 := mul_right_cancel₀ hπ.ne' h'
    have : 2 * (m - n) = 1 := by exact_mod_cast h''
    omega
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · exfalso
    have hk : (k₁ : ℝ) + 1 ≤ k₂ := by exact_mod_cast h
    have hmem : (k₁ : ℝ) * (2 * Real.pi) + Real.pi ∈ Set.Icc (g a) (g b) := by
      rw [hk₁, hk₂]
      constructor <;> nlinarith
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hab hg hmem
    obtain ⟨m, hm⟩ := hint t ht
    exact hodd m k₁ (hm ▸ hgt)
  · rw [hk₁, hk₂, h]
  · exfalso
    have hk : (k₂ : ℝ) + 1 ≤ k₁ := by exact_mod_cast h
    have hmem : (k₂ : ℝ) * (2 * Real.pi) + Real.pi ∈ Set.Icc (g b) (g a) := by
      rw [hk₁, hk₂]
      constructor <;> nlinarith
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hab hg hmem
    obtain ⟨m, hm⟩ := hint t ht
    exact hodd m k₂ (hm ▸ hgt)

/-- Two polar representations of the same vector have angles differing by `2πℤ`. -/
theorem same_angle {ρ ρ' θ θ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (h : (![ρ * Real.cos θ, ρ * Real.sin θ] : Plane) =
      ![ρ' * Real.cos θ', ρ' * Real.sin θ']) :
    ∃ n : ℤ, θ - θ' = n * (2 * Real.pi) := by
  have h0 : ρ * Real.cos θ = ρ' * Real.cos θ' := by simpa using congrFun h 0
  have h1 : ρ * Real.sin θ = ρ' * Real.sin θ' := by simpa using congrFun h 1
  have a := Real.cos_sq_add_sin_sq θ
  have b := Real.cos_sq_add_sin_sq θ'
  have hsq : ρ ^ 2 = ρ' ^ 2 := by
    calc ρ ^ 2 = (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 := by
          linear_combination (-ρ ^ 2) * a
      _ = (ρ' * Real.cos θ') ^ 2 + (ρ' * Real.sin θ') ^ 2 := by rw [h0, h1]
      _ = ρ' ^ 2 := by linear_combination ρ' ^ 2 * b
  have hρρ : ρ = ρ' := by nlinarith
  subst hρρ
  have hc : Real.cos θ = Real.cos θ' := mul_left_cancel₀ hρ.ne' h0
  have hs : Real.sin θ = Real.sin θ' := mul_left_cancel₀ hρ.ne' h1
  have hcos : Real.cos (θ - θ') = 1 := by
    rw [Real.cos_sub, hc, hs]; linear_combination b
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos
  exact ⟨n, hn.symm⟩

/-- The angle correction between the ellipse `(4 cos ψ, 5 sin ψ)` and the circle. -/
def qf (ψ : ℝ) : ℝ := Real.sin ψ * Real.cos ψ / (4 + Real.sin ψ ^ 2)

/-- A continuous polar angle of `(cos (t + φ) / 5, sin (t + φ) / 4)`. -/
def lift (φ t : ℝ) : ℝ := t + φ + Real.arctan (qf (t + φ))

theorem continuous_qf : Continuous qf := by
  unfold qf
  exact (by fun_prop : Continuous fun ψ => Real.sin ψ * Real.cos ψ).div (by fun_prop)
    (fun ψ => by positivity)

theorem continuous_lift (φ : ℝ) : Continuous (lift φ) := by
  unfold lift
  have h := continuous_qf
  fun_prop

theorem polar_aux (R ψ : ℝ) (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ (![R * Real.cos ψ / 5, R * Real.sin ψ / 4] : Plane) =
      ![ρ * Real.cos (ψ + Real.arctan (qf ψ)), ρ * Real.sin (ψ + Real.arctan (qf ψ))] := by
  have hd : 0 < 4 + Real.sin ψ ^ 2 := by positivity
  have hr : 0 < Real.sqrt (1 + qf ψ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hqd : qf ψ * (4 + Real.sin ψ ^ 2) = Real.sin ψ * Real.cos ψ := by
    rw [qf]; field_simp
  have hcs := Real.cos_sq_add_sin_sq ψ
  refine ⟨R * (4 + Real.sin ψ ^ 2) * Real.sqrt (1 + qf ψ ^ 2) / 20, by positivity, ?_⟩
  rw [Real.cos_add ψ, Real.sin_add ψ, Real.cos_arctan, Real.sin_arctan]
  funext i
  fin_cases i
  · simp
    field_simp
    linear_combination (5 * Real.sin ψ) * hqd
  · simp
    field_simp
    linear_combination (-4 * Real.cos ψ) * hqd + (-4 * Real.sin ψ) * hcs

theorem polar_lift (R φ : ℝ) (hR : 0 < R) (t : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ (![R * Real.cos (t + φ) / 5, R * Real.sin (t + φ) / 4] : Plane) =
      ![ρ * Real.cos (lift φ t), ρ * Real.sin (lift φ t)] :=
  polar_aux R (t + φ) hR

/-- Every continuous polar angle of the rotating frame coordinates advances by the
elapsed time, up to an error below `π`. -/
theorem winding_bounds (a b : ℝ) (hab : (![a, b] : Plane) ≠ 0) (θ : ℝ → ℝ)
    (hθ : Continuous θ)
    (hrep : ∀ t, ∃ ρ : ℝ, 0 < ρ ∧ (![a * Real.cos t - 4 / 5 * b * Real.sin t,
      5 / 4 * a * Real.sin t + b * Real.cos t] : Plane) =
        ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)])
    (t₁ : ℝ) (ht₁ : 0 ≤ t₁) :
    t₁ - Real.pi < θ t₁ - θ 0 ∧ θ t₁ - θ 0 < t₁ + Real.pi := by
  set z : ℂ := ⟨5 * a, 4 * b⟩ with hz_def
  have hz : z ≠ 0 := by
    intro h0
    apply hab
    have ha : 5 * a = 0 := congrArg Complex.re h0
    have hb : 4 * b = 0 := congrArg Complex.im h0
    funext i; fin_cases i <;> simp <;> linarith
  have hR : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hA : ‖z‖ * Real.cos (Complex.arg z) = 5 * a := Complex.norm_mul_cos_arg z
  have hB : ‖z‖ * Real.sin (Complex.arg z) = 4 * b := Complex.norm_mul_sin_arg z
  have hvec : ∀ t, (![a * Real.cos t - 4 / 5 * b * Real.sin t,
      5 / 4 * a * Real.sin t + b * Real.cos t] : Plane) =
      ![‖z‖ * Real.cos (t + Complex.arg z) / 5,
        ‖z‖ * Real.sin (t + Complex.arg z) / 4] := by
    intro t
    funext i
    fin_cases i <;> simp [Real.cos_add, Real.sin_add]
    · linear_combination (-(Real.cos t) / 5) * hA + (Real.sin t / 5) * hB
    · linear_combination (-(Real.sin t) / 4) * hA - (Real.cos t / 4) * hB
  have hint : ∀ t ∈ Set.Icc 0 t₁, ∃ k : ℤ,
      (fun s => θ s - lift (Complex.arg z) s) t = k * (2 * Real.pi) := by
    intro t _
    obtain ⟨ρ, hρ, h1⟩ := hrep t
    obtain ⟨ρ', hρ', h2⟩ := polar_lift ‖z‖ (Complex.arg z) hR t
    rw [hvec t] at h1
    exact same_angle hρ hρ' (h1.symm.trans h2)
  have hc : θ t₁ - lift (Complex.arg z) t₁ = θ 0 - lift (Complex.arg z) 0 :=
    const_of_two_pi_int (g := fun s => θ s - lift (Complex.arg z) s) ht₁
      ((hθ.sub (continuous_lift (Complex.arg z))).continuousOn) hint
  unfold lift at hc
  have e1 := Real.arctan_lt_pi_div_two (qf (t₁ + Complex.arg z))
  have e2 := Real.neg_pi_div_two_lt_arctan (qf (t₁ + Complex.arg z))
  have e3 := Real.arctan_lt_pi_div_two (qf (0 + Complex.arg z))
  have e4 := Real.neg_pi_div_two_lt_arctan (qf (0 + Complex.arg z))
  constructor <;> linarith

/-! ## A solution of the variational equation -/

/-- Multiplication by `i` on both complex coordinates `z` and `w`. -/
def Gm : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![-ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 0,
    -ContinuousLinearMap.proj 3, ContinuousLinearMap.proj 2]

/-- The linearization in the frame rotating with the orbit. -/
def Bm : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![gradCLM ![-4, -7 / 2, 1, 0], gradCLM ![7 / 2, 4, 0, 1],
    gradCLM ![-17 / 4, -4, 4, -7 / 2], gradCLM ![-4, -17 / 4, 7 / 2, -4]]

/-- The rotation by `9t/2` in both complex coordinates. -/
def Rm (t : ℝ) : Phase →L[ℝ] Phase :=
  Cf t • ContinuousLinearMap.id ℝ Phase + Sf t • Gm

/-- The linearized flow along the orbit: rotate, after flowing by `Bm`. -/
def Yex (t : ℝ) : Phase →L[ℝ] Phase := (Rm t).comp (NormedSpace.exp (t • Bm))

theorem Yex_zero : Yex 0 = ContinuousLinearMap.id ℝ Phase := by
  rw [Yex, zero_smul, NormedSpace.exp_zero]
  refine ContinuousLinearMap.ext fun w => ?_
  simp [Rm, Cf, Sf]

theorem hasDerivAt_Rm (t : ℝ) : HasDerivAt Rm
    ((-(9 / 2) * Sf t) • ContinuousLinearMap.id ℝ Phase + (9 / 2 * Cf t) • Gm) t :=
  ((hasDerivAt_Cf t).smul_const (ContinuousLinearMap.id ℝ Phase)).add
    ((hasDerivAt_Sf t).smul_const Gm)

theorem key_identity (t : ℝ) :
    (-(9 / 2) * Sf t) • ContinuousLinearMap.id ℝ Phase + (9 / 2 * Cf t) • Gm
      + (Rm t).comp Bm = (DX (orbit t)).comp (Rm t) := by
  refine ContinuousLinearMap.ext fun w => funext fun i => ?_
  have e := CS_one t
  fin_cases i <;> simp [Rm, Gm, Bm, DX_apply, hP, c₀, Fin.sum_univ_four, dotProduct]
  · linear_combination (4 * (Cf t * w 0 + 2 * Cf t * w 1 + 2 * Sf t * w 0
      + Sf t * w 1)) * e
  · linear_combination (-4 * (2 * Cf t * w 0 + Cf t * w 1 - Sf t * w 0
      - 2 * Sf t * w 1)) * e
  · linear_combination (4 * (2 * Cf t * w 0 + Cf t * w 1 - Cf t * w 2 + 2 * Cf t * w 3
      - Sf t * w 0 - 2 * Sf t * w 1 + 2 * Sf t * w 2 - Sf t * w 3)) * e
  · linear_combination (4 * (Cf t * w 0 + 2 * Cf t * w 1 - 2 * Cf t * w 2 + Cf t * w 3
      + 2 * Sf t * w 0 + Sf t * w 1 - Sf t * w 2 + 2 * Sf t * w 3)) * e

theorem hasDerivAt_Yex (t : ℝ) : HasDerivAt Yex
    ((fderiv ℝ (hamiltonianVectorField K₀) (orbit t)).comp (Yex t)) t := by
  have h := (hasDerivAt_Rm t).clm_comp (hasDerivAt_exp_smul_const' Bm t)
  rw [fderiv_X]
  refine h.congr_deriv ?_
  rw [Yex, ← ContinuousLinearMap.comp_assoc, ← key_identity t]
  conv_rhs => rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc]
  rfl

/-! ## The counterexample -/

/-- The clock: it jumps by six periods at time `T₀`. -/
def σ₀ (t : ℝ) : ℝ := if t < T₀ then t else t + 6 * T₀

theorem σ₀_strictMono : StrictMono σ₀ := by
  intro s t hst
  have hT := T₀_pos
  unfold σ₀
  split_ifs <;> linarith

theorem σ₀_zero : σ₀ 0 = 0 := by simp [σ₀, T₀_pos]

theorem σ₀_T : σ₀ T₀ = 7 * T₀ := by simp [σ₀]; ring

theorem orbit_σ₀ (t : ℝ) : orbit (σ₀ t) = orbit t := by
  unfold σ₀
  split_ifs
  · rfl
  · simpa using orbit_add_period t 6

/-- The seven-fold cover winds by more than one turn. -/
theorem wind_seven : HasTransverseWindingAboveOne K₀ orbit (7 * T₀) := by
  intro Y hY0 hY v hv hcoord θ hθ hrep
  have hform := core Y hY0 hY v hv
  have h0 : transverseFrameCoordinates (TangentialHessian.grad K₀ (orbit 0)) v =
      ![ξ1 (fun s => Y s v) 0, ξ2 (fun s => Y s v) 0] := by
    have h := tfc_orbit (fun s => Y s v) 0
    simpa [hY0] using h
  have hab : (![ξ1 (fun s => Y s v) 0, ξ2 (fun s => Y s v) 0] : Plane) ≠ 0 := by
    rw [← h0]; exact hcoord
  have hrep' : ∀ t, ∃ ρ : ℝ, 0 < ρ ∧
      (![ξ1 (fun s => Y s v) 0 * Real.cos t - 4 / 5 * ξ2 (fun s => Y s v) 0 * Real.sin t,
        5 / 4 * ξ1 (fun s => Y s v) 0 * Real.sin t
          + ξ2 (fun s => Y s v) 0 * Real.cos t] : Plane) =
        ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)] := by
    intro t; rw [← hform t]; exact hrep t
  obtain ⟨hlo, -⟩ := winding_bounds _ _ hab θ hθ hrep' (7 * T₀)
    (by have := T₀_pos; positivity)
  unfold T₀ at hlo ⊢
  linarith [Real.pi_pos]

/-- A tangent vector along the first frame direction at `orbit 0`. -/
def v₁ : Phase := ![1, -1, -2, -2]

/-- The single orbit winds by less than one turn. -/
theorem not_wind_one : ¬ HasTransverseWindingAboveOne K₀ orbit T₀ := by
  intro h
  have hv : fderiv ℝ K₀ (orbit 0) v₁ = 0 := by
    rw [fderiv_K₀, gradCLM_apply, dP_orbit]
    simp [gO, v₁, dotProduct, Fin.sum_univ_four, Cf, Sf]
  have hξ1 : ξ1 (fun s => Yex s v₁) 0 = 45 / 2 := by
    simp [ξ1, Yex_zero, v₁, Cf, Sf]
    norm_num
  have hξ2 : ξ2 (fun s => Yex s v₁) 0 = 0 := by
    simp [ξ2, Yex_zero, v₁, Cf, Sf]
  have hcoord : transverseFrameCoordinates (TangentialHessian.grad K₀ (orbit 0)) v₁ ≠ 0 := by
    have e := tfc_orbit (fun s => Yex s v₁) 0
    simp only [Yex_zero, ContinuousLinearMap.id_apply] at e
    rw [e, hξ1, hξ2]
    intro h0
    have := congrFun h0 0
    norm_num at this
  have hrep : ∀ t, ∃ ρ : ℝ, 0 < ρ ∧
      transverseFrameCoordinates (TangentialHessian.grad K₀ (orbit t)) (Yex t v₁) =
        ![ρ * Real.cos (lift 0 t), ρ * Real.sin (lift 0 t)] := by
    intro t
    obtain ⟨ρ, hρ, e⟩ := polar_lift (225 / 2) 0 (by norm_num) t
    refine ⟨ρ, hρ, ?_⟩
    rw [core Yex Yex_zero hasDerivAt_Yex v₁ hv t, hξ1, hξ2, ← e]
    funext i
    fin_cases i <;> simp <;> ring
  have hlt := h Yex Yex_zero hasDerivAt_Yex v₁ hv hcoord (lift 0) (continuous_lift 0) hrep
  have e1 : lift 0 T₀ = T₀ + Real.arctan (qf T₀) := by simp [lift]
  have e0 : lift 0 0 = 0 := by simp [lift, qf]
  rw [e1, e0] at hlt
  have := Real.arctan_lt_pi_div_two (qf T₀)
  unfold T₀ at hlt this
  linarith [Real.pi_pos]

end

end BirkhoffGlobalSection.ClosedWindingCounterexample

open BirkhoffGlobalSection BirkhoffGlobalSection.ClosedWindingCounterexample

theorem solution : ¬ (∀ (μ c : ℝ) (M : RegularizationModel μ c) (S : Set Phase)
    (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c ∩ M.toModel ⁻¹' S) x T)
    (y : ℝ → Phase) (T' : ℝ)
    (hy : IsPeriodicHamiltonianSolutionIn M.modelHamiltonian S y T')
    (σ : ℝ → ℝ)
    (hσ : StrictMono σ) (hσ0 : σ 0 = 0) (hσT : σ T = T')
    (hrel : ∀ t : ℝ, y (σ t) = M.toModel (x t))
    (hwind : HasTransverseWindingAboveOne M.modelHamiltonian y T'),
    HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T) := by
  intro h
  have hx : IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian 0 c₀)
      (leftEnergyComponent 0 c₀ ∩ idModel.toModel ⁻¹' Set.univ) orbit T₀ :=
    ⟨T₀_pos, fun t => ⟨orbit_mem t, trivial⟩, hasDerivAt_orbit,
      by simpa using orbit_add_period 0 1⟩
  have hy : IsPeriodicHamiltonianSolutionIn idModel.modelHamiltonian Set.univ orbit
      (7 * T₀) :=
    ⟨by have := T₀_pos; positivity, fun _ => trivial, hasDerivAt_orbit,
      by simpa using orbit_add_period 0 7⟩
  exact not_wind_one (h 0 c₀ idModel Set.univ orbit T₀ hx orbit (7 * T₀) hy σ₀
    σ₀_strictMono σ₀_zero σ₀_T (fun t => orbit_σ₀ t) wind_seven)
