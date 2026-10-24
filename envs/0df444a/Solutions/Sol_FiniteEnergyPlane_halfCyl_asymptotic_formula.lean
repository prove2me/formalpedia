-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_asymptotic_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T15:36:53.955994+00:00
-- url     : https://prove2.me/submissions/607b32ca-56b3-4930-8479-9e7a0cbedc80

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_JHolomorphic_bounded_iteratedFDeriv_of_sobolevNorm_le
import Theorems.Thm_FiniteEnergyPlane_halfCyl_rescaled_exp_conv

set_option linter.all false

section HD_a

/-! Global existence for linear ODEs `x' = L t (x t)` with bounded coefficients (Picard series). -/

open scoped Topology
open Set Filter

namespace HDecay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end HDecay

end HD_a

section HD_b

/-! Fundamental solution of `Ψ' = J₀ S∞ Ψ`, its inverse, and the sup-norm gap estimate. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

abbrev Op (n : ℕ) := Vec n →L[ℝ] Vec n

/-- matrices as operators -/
noncomputable def TL (n : ℕ) : Mat n ≃L[ℝ] (Op n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

lemma TL_mul (M N : Mat n) : TL n (M * N) = TL n M * TL n N :=
  map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)) M N

lemma TL_one : TL n 1 = 1 := map_one (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n))

end HDecay

end HD_b

section HD_c

/-! Sup-norm gap estimate for the nondegenerate asymptotic operator `-J₀ ∂ₜ - S∞`. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

/-- `J₀` as an operator. -/
noncomputable abbrev Jop (n : ℕ) : Op n := TL n (J₀ n)

lemma Jop_Jop (v : Vec n) : Jop n (Jop n v) = -v := by
  have : Jop n * Jop n = -1 := by
    rw [Jop, ← TL_mul, Matrix.J_squared, map_neg, TL_one]
  have h := congrArg (fun T : Op n => T v) this
  simpa using h

end HDecay

end HD_c

section HD_d

/-! Partial derivatives on the half-cylinder `Ω = (0, ∞) × ℝ`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

/-- The open half-cylinder (as a strip). -/
def Ω : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ

lemma isOpen_Ω : IsOpen Ω := isOpen_Ioi.prod isOpen_univ

lemma mem_Ω {s t : ℝ} (hs : 0 < s) : (s, t) ∈ Ω := ⟨hs, trivial⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `∂ₛu`. -/
noncomputable def pS (u : ℝ × ℝ → F) (x : ℝ × ℝ) : F := fderiv ℝ u x (1, 0)
/-- `∂ₜu`. -/
noncomputable def pT (u : ℝ × ℝ → F) (x : ℝ × ℝ) : F := fderiv ℝ u x (0, 1)

/-- Smooth on `Ω`. -/
abbrev Sm (u : ℝ × ℝ → F) : Prop := ContDiffOn ℝ ∞ u Ω

lemma Sm.diffAt {u : ℝ × ℝ → F} (hu : Sm u) {x : ℝ × ℝ} (hx : x ∈ Ω) :
    DifferentiableAt ℝ u x :=
  (hu.contDiffAt (isOpen_Ω.mem_nhds hx)).differentiableAt (by simp)

lemma Sm.hasDerivAt_s {u : ℝ × ℝ → F} (hu : Sm u) {s t : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => u (σ, t)) (pS u (s, t)) s := by
  have h := (hu.diffAt (mem_Ω (t := t) hs)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  exact h

lemma Sm.hasDerivAt_t {u : ℝ × ℝ → F} (hu : Sm u) {s t : ℝ} (hs : 0 < s) :
    HasDerivAt (fun τ => u (s, τ)) (pT u (s, t)) t := by
  have h := (hu.diffAt (mem_Ω (t := t) hs)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  exact h

/-- `t`-periodicity -/
def TPer (u : ℝ × ℝ → F) : Prop := ∀ s t : ℝ, u (s, t + 1) = u (s, t)

lemma TPer.periodic {u : ℝ × ℝ → F} (hu : TPer u) (s : ℝ) :
    Function.Periodic (fun t => u (s, t)) 1 := fun t => hu s t

/-! ### Operator-valued coefficients -/

variable {n : ℕ}

/-- matrix fields as operator fields -/
lemma TL_eq_sum (M : Mat n) :
    TL n M = ∑ i, ∑ j, M i j • TL n (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul]
  congr 1
  ext a b
  simp [Matrix.single_apply]

lemma contDiff_TL {k : WithTop ℕ∞} (S : ℝ × ℝ → Mat n)
    (hS : ∀ i j, ContDiff ℝ k (fun p : ℝ × ℝ => S p i j)) :
    ContDiff ℝ k (fun p => TL n (S p)) := by
  have : (fun p => TL n (S p)) = fun p => ∑ i, ∑ j, S p i j • TL n (Matrix.single i j 1) := by
    funext p; exact TL_eq_sum _
  rw [this]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hS i j).smul contDiff_const

lemma contDiff_TL1 {k : WithTop ℕ∞} (S : ℝ → Mat n)
    (hS : ∀ i j, ContDiff ℝ k (fun t => S t i j)) :
    ContDiff ℝ k (fun t => TL n (S t)) := by
  have : (fun t => TL n (S t)) = fun t => ∑ i, ∑ j, S t i j • TL n (Matrix.single i j 1) := by
    funext p; exact TL_eq_sum _
  rw [this]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hS i j).smul contDiff_const

end HDecay

end HD_d

section HD_e

/-! `t`-integrals over a period: differentiation in `s` and integration by parts in `t`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end HD_e

section HD_f

/-! Bounds on the coefficient field `S` from its `C^∞` convergence to `S∞`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

end HDecay

end HD_f

section HD_g

/-! Second derivative of the energy `∫₀¹ |η(s, t)|² dt`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

section energy

variable (A : ℝ × ℝ → Op n) (η : ℝ × ℝ → Vec n)

/-- residual `∂ₛη + J₀ ∂ₜη + A η` -/
noncomputable def res (x : ℝ × ℝ) : Vec n := pS η x + Jop n (pT η x) + A x (η x)

variable {A η}

end energy

end HDecay

end HD_g

section HD_h

/-! Jensen, the `L²` gap estimate, and two one-variable decay lemmas. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end HD_h

section HD_i

/-! Generic lower bounds for the energy's second derivative. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end HD_i

section HD_j

/-! One-variable lemmas used to pass from energy inequalities to decay. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

end HDecay

end HD_j

section AF_a

/-! Gap estimate with kernel: periodic loops are sup-close to periodic solutions. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_a

section AF_b

/-! Cauchy–Schwarz for `Ip` and the differential inequality for `α = ⟨ζ, ∂ₛζ⟩ / |ζ|²`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_b

section AF_c

/-! One-variable lemmas: forward positivity (unique continuation) and barriers. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

end HDecay

end AF_c

section AF_d

/-! Convergence of `α` under an integrable (exponentially small) defect. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

section

variable (α α1 q F ε : ℝ → ℝ) (s1 K d C0 δ0 : ℝ)

variable {α α1 q F ε s1 K d C0 δ0}

end

end HDecay

end AF_d

section AF_e

/-! Exponential rate for `α → μ` given a spectral gap inequality. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

variable {α α1 q F ε : ℝ → ℝ} {s1 K d C0 δ0 : ℝ}

end HDecay

end AF_e

section AF_f

/-! Exponentially small coefficients from `IsExpAsymptoticTo`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_f

section AF_g

/-! The quantities `F, D, G, α, q` of a solution and their derivatives. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

section sol

variable (A : ℝ × ℝ → Op n) (ζ : ℝ × ℝ → Vec n)

variable {A ζ}

end sol

end HDecay

end AF_g

section AF_h

/-! Unique continuation: `‖ζ(s)‖_{L²} > 0` for all `s ≥ s₀` once it is positive at `s₀`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_h

section AF_i

/-! The `α`-hypotheses for a solution of the linear Cauchy–Riemann equation. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_i

section AF_j

/-! Spectral gap inequality for `A∞ - μ`, valid for every `μ ∈ ℝ`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_j

section AF_k

/-! The gap inequality `|α - μ| ≤ κ (q + ε)` near `μ`, for a solution of the linear CR equation. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_k

section AF_l

/-! Exponential convergence of `α` to a limit `μ ≤ δ₀` for a solution. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_l

section AF_m

/-! A one-dimensional mean value inequality: `f'' ≥ -g`, `f ≥ 0` ⇒ `f(a) ≤ ∫ f + ∫ g`. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

end HDecay

end AF_m

section AF_n

/-! Pointwise decay of `‖∂ₛζ - μζ‖²_{L²}` relative to `‖ζ‖²_{L²}`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

/-- `∂ₛζ - μζ` -/
noncomputable def ηm (ζ : ℝ × ℝ → Vec n) (μ : ℝ) : ℝ × ℝ → Vec n := fun x => pS ζ x - μ • ζ x

end HDecay

end AF_n

section AF_o

/-! `‖∂ₛζ - μζ‖²_{L²}(s) ≤ C e^{-a s} ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_o

section AF_p

/-! The rescaled solution `χ = e^{-μs} ζ`: derivatives and two-sided `L²` bounds. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

/-- `χ = e^{-μs} ζ` -/
noncomputable def χr (ζ : ℝ × ℝ → Vec n) (μ : ℝ) : ℝ × ℝ → Vec n :=
  fun x => Real.exp (-(μ * x.1)) • ζ x

lemma contDiff_expw (μ : ℝ) : ContDiff ℝ ∞ (fun x : ℝ × ℝ => Real.exp (-(μ * x.1))) :=
  Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).neg)

lemma Sm.χr {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) : Sm (χr ζ μ) :=
  (contDiff_expw μ).contDiffOn.smul hζ

lemma TPer.χr {ζ : ℝ × ℝ → Vec n} (hζ : TPer ζ) (μ : ℝ) : TPer (χr ζ μ) := fun s t => by
  simp only [HDecay.χr, hζ s t]

lemma pS_χr {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) {s t : ℝ} (hs : 0 < s) :
    pS (χr ζ μ) (s, t) = Real.exp (-(μ * s)) • ηm ζ μ (s, t) := by
  have h1 := (hζ.χr μ).hasDerivAt_s (t := t) hs
  have he : HasDerivAt (fun σ : ℝ => Real.exp (-(μ * σ))) (Real.exp (-(μ * s)) * (-μ)) s := by
    have := ((hasDerivAt_id s).const_mul μ).neg.exp
    simpa using this
  have h2 := he.smul (hζ.hasDerivAt_s (t := t) hs)
  have := h1.unique h2
  rw [this]
  simp only [ηm, smul_sub, smul_smul]
  module

lemma pT_χr {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) {s t : ℝ} (hs : 0 < s) :
    pT (χr ζ μ) (s, t) = Real.exp (-(μ * s)) • pT ζ (s, t) := by
  have h1 := (hζ.χr μ).hasDerivAt_t (t := t) hs
  have h2 := (hζ.hasDerivAt_t (t := t) hs).const_smul (Real.exp (-(μ * s)))
  exact h1.unique h2

/-- the equation for `χ`, in the form needed for the gap estimate -/
lemma χr_eq {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (Sinf : ℝ → Mat n) (μ : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    -(Jop n (pT (χr ζ μ) (s, t))) - TL n (Sinf t) (χr ζ μ (s, t)) - μ • χr ζ μ (s, t) =
      pS (χr ζ μ) (s, t) + (A (s, t) - TL n (Sinf t)) (χr ζ μ (s, t)) := by
  have h0 := hres0 (s, t) (mem_Ω hs)
  rw [pT_χr hζ μ hs, pS_χr hζ μ hs]
  show -(Jop n (Real.exp (-(μ * s)) • pT ζ (s, t))) - TL n (Sinf t) (Real.exp (-(μ * s)) • ζ (s, t)) -
    μ • (Real.exp (-(μ * s)) • ζ (s, t)) = Real.exp (-(μ * s)) • ηm ζ μ (s, t) +
      (A (s, t) - TL n (Sinf t)) (Real.exp (-(μ * s)) • ζ (s, t))
  simp only [res] at h0
  have e : pS ζ (s, t) = -(Jop n (pT ζ (s, t))) - A (s, t) (ζ (s, t)) := by
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h0]; abel
  simp only [ηm, e, map_smul, ContinuousLinearMap.sub_apply, smul_sub, smul_neg, smul_smul]
  module

end HDecay

end AF_p

section AF_q

/-! `∫ |χ(s₁) - χ(s₀)| ≤ ∫_{s₀}^{s₁} ‖∂ₛχ‖_{L²}`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_q

section AF_r

/-! Uniform exponential convergence of `χ(s, ·)` to a nonzero periodic solution `Ψ(·) k`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_r

section AF_s

/-! One-dimensional Caccioppoli and Sobolev inequalities. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_s

section AF_t

/-! The third `s`-derivative of the coefficient decays exponentially. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_t

section AF_u

/-! Second energy level: residual identities and an energy inequality with a scalar weight. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_u

section AF_v

/-! `‖∂ₛ(∂ₛζ - μζ)‖²_{L²}(s) ≤ C ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_v

section AF_w

/-! `‖∂ₛ(∂ₛζ - μζ)‖²_{L²}(s) ≤ C ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_w

section AF_x

/-! Smoothness of the fundamental solution; the limit `Ψ(·) k` is an eigenfunction. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_x

section AF_y

/-! Stage E: exponential `C⁰` convergence of `e^{-μs} ζ` to an eigenfunction, with `C¹` bounds. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_y

section AF_z

/-! Stage E assembled. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_z

section AF_F1

/-! Stage F1: the graph almost complex structure on `ℂ × ℝ^{2n}`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

/-- the coupling term `w ↦ ((a, x) ↦ (0, Re a • J₀ w + Im a • w))` -/
noncomputable def Λf (w : Vec n) : ℂ × Vec n →L[ℝ] ℂ × Vec n :=
  (0 : ℂ × Vec n →L[ℝ] ℂ).prod
    (((ContinuousLinearMap.smulRight (Complex.reCLM : ℂ →L[ℝ] ℝ) (Jop n w)) +
      (ContinuousLinearMap.smulRight (Complex.imCLM : ℂ →L[ℝ] ℝ) w)).comp
      (ContinuousLinearMap.fst ℝ ℂ (Vec n)))

lemma Λf_apply (w : Vec n) (a : ℂ) (x : Vec n) :
    Λf w (a, x) = (0, a.re • Jop n w + a.im • w) := by
  simp [Λf]

noncomputable def Λlin (n : ℕ) : Vec n →ₗ[ℝ] (ℂ × Vec n →L[ℝ] ℂ × Vec n) where
  toFun w := Λf w
  map_add' v w := by
    refine ContinuousLinearMap.ext fun ⟨a, x⟩ => ?_
    simp only [ContinuousLinearMap.add_apply, Λf_apply, map_add, smul_add, Prod.mk_add_mk, add_zero]
    congr 1; abel
  map_smul' c w := by
    refine ContinuousLinearMap.ext fun ⟨a, x⟩ => ?_
    simp only [ContinuousLinearMap.smul_apply, Λf_apply, map_smul, RingHom.id_apply, Prod.smul_mk,
      smul_zero, smul_add, smul_smul, mul_comm]

noncomputable def Λc (n : ℕ) : Vec n →L[ℝ] (ℂ × Vec n →L[ℝ] ℂ × Vec n) :=
  LinearMap.toContinuousLinearMap (Λlin n)

lemma Λc_apply (w : Vec n) (a : ℂ) (x : Vec n) :
    Λc n w (a, x) = (0, a.re • Jop n w + a.im • w) := by
  show Λf w (a, x) = _
  exact Λf_apply w a x

/-- the constant part `(a, x) ↦ (i a, J₀ x)` -/
noncomputable def Jc (n : ℕ) : ℂ × Vec n →L[ℝ] ℂ × Vec n :=
  ((ContinuousLinearMap.lsmul ℝ ℂ Complex.I).comp (ContinuousLinearMap.fst ℝ ℂ (Vec n))).prod
    ((Jop n).comp (ContinuousLinearMap.snd ℝ ℂ (Vec n)))

lemma Jc_apply (a : ℂ) (x : Vec n) : Jc n (a, x) = (Complex.I * a, Jop n x) := by
  simp [Jc]

/-- the almost complex structure `J_B(z, v) = Jc + Λ(B(z) v)` -/
noncomputable def Jof (B : ℂ → Op n) (p : ℂ × Vec n) : ℂ × Vec n →L[ℝ] ℂ × Vec n :=
  Jc n + Λc n (B p.1 p.2)

lemma Jof_apply (B : ℂ → Op n) (p : ℂ × Vec n) (a : ℂ) (x : Vec n) :
    Jof B p (a, x) = (Complex.I * a, Jop n x + (a.re • Jop n (B p.1 p.2) + a.im • B p.1 p.2)) := by
  simp only [Jof, ContinuousLinearMap.add_apply, Jc_apply, Λc_apply, Prod.mk_add_mk, add_zero]

lemma Jof_sq (B : ℂ → Op n) (p : ℂ × Vec n) :
    (Jof B p).comp (Jof B p) = -ContinuousLinearMap.id ℝ (ℂ × Vec n) := by
  refine ContinuousLinearMap.ext fun ⟨a, x⟩ => ?_
  rw [ContinuousLinearMap.comp_apply, Jof_apply, Jof_apply]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.neg_mk]
  refine Prod.ext ?_ ?_
  · simp only; rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  · simp only [map_add, map_smul, Jop_Jop, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub, sub_zero, zero_add, neg_smul, smul_neg]
    abel

lemma Jof_contDiff {B : ℂ → Op n} (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (Jof B) := by
  have h : ContDiff ℝ ∞ (fun p : ℂ × Vec n => B p.1 p.2) :=
    (hB.comp contDiff_fst).clm_apply contDiff_snd
  exact contDiff_const.add ((Λc n).contDiff.comp h)

lemma Jof_almostComplex {B : ℂ → Op n} (hB : ContDiff ℝ ∞ B) :
    JHolomorphic.IsAlmostComplexOn (Jof B) univ :=
  ⟨isOpen_univ, (Jof_contDiff hB).contDiffOn, fun p _ => Jof_sq B p⟩

end HDecay

end AF_F1

section AF_F2

/-! Stage F2: `C^∞_loc` convergence of coefficients gives `C^∞_loc` convergence of `Jof`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma norm_iteratedFDeriv_clm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (j : ℕ) (p : E) :
    ‖iteratedFDeriv ℝ j L p‖ ≤ ‖L‖ * (‖p‖ + 1) := by
  rcases j with _ | j
  · rw [norm_iteratedFDeriv_zero]
    exact (L.le_opNorm p).trans (mul_le_mul_of_nonneg_left (by linarith only) (norm_nonneg _))
  · rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.norm_map]
    have hf : (fun y => fderiv ℝ L y) = fun _ => L := funext fun y => L.fderiv
    rw [hf]
    rcases j with _ | j
    · rw [norm_iteratedFDeriv_zero]
      exact le_mul_of_one_le_right (norm_nonneg L) (by linarith only [norm_nonneg p])
    · rw [iteratedFDeriv_succ_const]
      have h0 : ‖(0 : E → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) (E →L[ℝ] F)) p‖ = 0 :=
        ContinuousMultilinearMap.opNorm_zero
      refine (le_of_eq h0).trans ?_
      exact mul_nonneg (norm_nonneg _) (by linarith only [norm_nonneg p])

theorem Jof_conv {B : ℕ → ℂ → Op n} {Binf : ℂ → Op n} (hB : ∀ ν, ContDiff ℝ ∞ (B ν))
    (hBinf : ContDiff ℝ ∞ Binf) (hc : JHolomorphic.TendstoCInftyLocOn B Binf univ) :
    JHolomorphic.TendstoCInftyLocOn (fun ν => Jof (B ν)) (Jof Binf) univ := by
  intro K _ hK m
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set R' := max R 0
  have hKR : ∀ p ∈ K, ‖p‖ ≤ R' := fun p hp => by
    have := hR hp; rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hR0 : (0:ℝ) ≤ R' := le_max_right _ _
  have hΛ := norm_nonneg (Λc n)
  set c := (‖Λc n‖ + 1) * (R' + 1) * 2 ^ m
  have hc0 : 0 < c :=
    mul_pos (mul_pos (by linarith only [hΛ]) (by linarith only [hR0])) (pow_pos two_pos m)
  set δ := ε / (2 * c)
  have hδ : 0 < δ := div_pos hε (mul_pos two_pos hc0)
  have hev : ∀ i ∈ Finset.range (m + 1), ∀ᶠ ν in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) R',
      dist (iteratedFDeriv ℝ i Binf z) (iteratedFDeriv ℝ i (B ν) z) < δ := fun i _ =>
    Metric.tendstoUniformlyOn_iff.1 (hc _ (subset_univ _) (isCompact_closedBall 0 R') i) δ hδ
  filter_upwards [(Finset.eventually_all _).2 hev] with ν hν p hp
  set D : ℂ → Op n := fun z => B ν z - Binf z
  have hD : ContDiff ℝ ∞ D := (hB ν).sub hBinf
  have hg : ContDiff ℝ ∞ (fun q : ℂ × Vec n => D q.1 q.2) :=
    (hD.comp contDiff_fst).clm_apply contDiff_snd
  have e1 : (fun q => Jof (B ν) q) - (fun q => Jof Binf q) = (Λc n) ∘ fun q : ℂ × Vec n => D q.1 q.2 := by
    funext q
    simp only [Pi.sub_apply, Function.comp, Jof, D, ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [dist_eq_norm, norm_sub_rev, ← iteratedFDeriv_sub_apply
    ((Jof_contDiff (hB ν)).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))
    ((Jof_contDiff hBinf).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)), e1]
  refine lt_of_le_of_lt ((Λc n).norm_iteratedFDeriv_comp_left hg.contDiffAt
    (by exact_mod_cast le_top)) ?_
  have hb := norm_iteratedFDeriv_clm_apply (f := fun q : ℂ × Vec n => D q.1)
    (g := fun q : ℂ × Vec n => q.2) (hD.comp contDiff_fst) contDiff_snd p
    (n := m) (by exact_mod_cast le_top)
  have hpR := hKR p hp
  have hterm : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun q : ℂ × Vec n => D q.1) p‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun q : ℂ × Vec n => q.2) p‖ ≤ (m.choose i : ℝ) * δ * (R' + 1) := by
    intro i hi
    have h1 : ‖iteratedFDeriv ℝ i (fun q : ℂ × Vec n => D q.1) p‖ ≤ δ := by
      have e2 : (fun q : ℂ × Vec n => D q.1) = D ∘ (ContinuousLinearMap.fst ℝ ℂ (Vec n)) := rfl
      rw [e2, (ContinuousLinearMap.fst ℝ ℂ (Vec n)).iteratedFDeriv_comp_right hD p
        (by exact_mod_cast le_top)]
      refine ((iteratedFDeriv ℝ i D _).norm_compContinuousLinearMap_le _).trans ?_
      have hfst : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℂ (Vec n)‖ ≤ 1 :=
        Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_fst_le _ _ _
      have hz : (ContinuousLinearMap.fst ℝ ℂ (Vec n)) p ∈ Metric.closedBall (0:ℂ) R' := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_fst_le p).trans hpR
      have hd := hν i hi _ hz
      rw [dist_eq_norm, norm_sub_rev, ← iteratedFDeriv_sub_apply
        ((hB ν).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))
        (hBinf.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))] at hd
      exact (mul_le_of_le_one_right (norm_nonneg _) hfst).trans hd.le
    have h2 : ‖iteratedFDeriv ℝ (m - i) (fun q : ℂ × Vec n => q.2) p‖ ≤ R' + 1 := by
      have := norm_iteratedFDeriv_clm_le (ContinuousLinearMap.snd ℝ ℂ (Vec n)) (m - i) p
      have hs := ContinuousLinearMap.norm_snd_le ℝ ℂ (Vec n)
      refine this.trans ?_
      calc ‖ContinuousLinearMap.snd ℝ ℂ (Vec n)‖ * (‖p‖ + 1) ≤ 1 * (R' + 1) :=
            mul_le_mul hs (by linarith only [hpR]) (by linarith only [norm_nonneg p]) zero_le_one
        _ = R' + 1 := one_mul _
    have hc0 : (0:ℝ) ≤ m.choose i := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 (norm_nonneg _) (mul_nonneg hc0 hδ.le)
  have hsum := (hb.trans (Finset.sum_le_sum hterm))
  have h2m : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  rw [← Finset.sum_mul, ← Finset.sum_mul, h2m] at hsum
  calc ‖Λc n‖ * ‖iteratedFDeriv ℝ m (fun q : ℂ × Vec n => D q.1 q.2) p‖
      ≤ ‖Λc n‖ * (2 ^ m * δ * (R' + 1)) := mul_le_mul_of_nonneg_left hsum hΛ
    _ ≤ c * δ := by
        have : (0:ℝ) ≤ 2 ^ m * δ * (R' + 1) :=
          mul_nonneg (mul_nonneg (pow_nonneg zero_le_two m) hδ.le) (by linarith only [hR0])
        have hcδ : c * δ = ‖Λc n‖ * (2 ^ m * δ * (R' + 1)) + 2 ^ m * δ * (R' + 1) := by
          simp only [c]; ring
        rw [hcδ]; exact le_add_of_nonneg_right this
    _ < ε := by
        have hcδ : c * δ = ε / 2 := by
          simp only [δ]; rw [mul_div_assoc', mul_comm 2 c, mul_div_mul_left _ _ hc0.ne']
        rw [hcδ]; exact half_lt_self hε

end HDecay

end AF_F2

section AF_F3

/-! Stage F3: the shifted coefficients `B_ν(a) = S(σ_ν + Re a, Im a) + μ` converge in `C^∞_loc`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma cle_iter {G E F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (g : G ≃L[ℝ] E) (f : E → F)
    (x : G) (i : ℕ) :
    iteratedFDeriv ℝ i (f ∘ g) x =
      (iteratedFDeriv ℝ i f (g x)).compContinuousLinearMap fun _ => (g : G →L[ℝ] E) := by
  simp only [← iteratedFDerivWithin_univ]
  have := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) i
  simpa using this

lemma norm_cle_iter_le {G E F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : G ≃L[ℝ] E) (f : E → F) (x : G) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (f ∘ g) x‖ ≤
      ‖iteratedFDeriv ℝ i f (g x)‖ * ‖(g : G →L[ℝ] E)‖ ^ i := by
  rw [cle_iter]
  refine ((iteratedFDeriv ℝ i f (g x)).norm_compContinuousLinearMap_le _).trans (le_of_eq ?_)
  simp [Finset.prod_const]

lemma norm_iter_smul_const_le {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : X → ℝ) (hg : ContDiff ℝ ∞ g) (c : F)
    (m : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ m (fun y => g y • c) x‖ ≤ ‖iteratedFDeriv ℝ m g x‖ * ‖c‖ := by
  set L : ℝ →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight c
  have e : (fun y => g y • c) = L ∘ g := by funext y; simp [L]
  rw [e]
  refine (L.norm_iteratedFDeriv_comp_left hg.contDiffAt (WithTop.coe_le_coe.2 le_top)).trans ?_
  have hL : ‖L‖ ≤ ‖c‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_of_le_one_left (norm_nonneg c) (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ))
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hL (norm_nonneg _)

lemma norm_iter_TL_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (g : X → Mat n)
    (hg : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (m : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ m (fun x => TL n (g x)) x‖ ≤
      ∑ i, ∑ j, ‖iteratedFDeriv ℝ m (fun x => g x i j) x‖ * ‖TL n (Matrix.single i j 1)‖ := by
  have e : (fun x => TL n (g x)) = fun x => ∑ i, ∑ j, g x i j • TL n (Matrix.single i j 1) :=
    funext fun x => TL_eq_sum _
  rw [e, iteratedFDeriv_fun_sum_apply (f := fun i x => ∑ j, g x i j • TL n (Matrix.single i j 1))
    (fun i _ => (ContDiff.sum fun j _ =>
    (hg i j).smul contDiff_const).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [iteratedFDeriv_fun_sum_apply (f := fun j x => g x i j • TL n (Matrix.single i j 1)) (fun j _ =>
    ((hg i j).smul contDiff_const).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact norm_iter_smul_const_le _ (hg i j) _ m x

/-- `C^∞` decay of `TL S - TL S∞`, uniformly in `t`. -/
theorem Dop_decay (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (d : ℝ) (hd : 0 < d)
    (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d) (m : ℕ) :
    ∀ ε > 0, ∃ s₁, ∀ s ≥ s₁, ∀ t,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => TL n (S p) - TL n (Sinf p.2)) (s, t)‖ ≤ ε := by
  intro ε hε
  have h := fun i j => (hSas i j).2 m
  choose Cf s1f hs1f using h
  set Ctot := ∑ i, ∑ j, |Cf i j| * ‖TL n (Matrix.single i j 1)‖
  set s1t := ∑ i, ∑ j, |s1f i j|
  have hs1 : ∀ i j, s1f i j ≤ s1t := by
    intro i j
    refine (le_abs_self _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, |s1f i j|)
      (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => |s1f i j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
  have ht : Tendsto (fun s => Ctot * Real.exp (-(d * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => d * s) atTop atTop := tendsto_id.const_mul_atTop hd
    have : Tendsto (fun s => Real.exp (-(d * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa using this.const_mul Ctot
  obtain ⟨s2, hs2⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds hε))
  refine ⟨max s1t s2, fun s hs t => ?_⟩
  have e : (fun p : ℝ × ℝ => TL n (S p) - TL n (Sinf p.2)) =
      fun p => TL n (S p - Sinf p.2) := funext fun p => (map_sub _ _ _).symm
  rw [e]
  have hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (S p - Sinf p.2) i j) := fun i j => by
    simp only [Matrix.sub_apply]
    exact (hS i j).sub ((hSinf' i j).comp contDiff_snd)
  refine (norm_iter_TL_le _ hg m (s, t)).trans ?_
  refine le_trans ?_ (hs2 s (le_trans (le_max_right _ _) hs))
  simp only [Ctot, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hb := hs1f i j s (le_trans (hs1 i j) (le_trans (le_max_left _ _) hs)) t
  simp only [Matrix.sub_apply] at hb ⊢
  have hc := norm_nonneg (TL n (Matrix.single i j 1))
  calc ‖iteratedFDeriv ℝ m (fun x : ℝ × ℝ => S x i j - Sinf x.2 i j) (s, t)‖ *
        ‖TL n (Matrix.single i j 1)‖
      ≤ (Cf i j * Real.exp (-(d * s))) * ‖TL n (Matrix.single i j 1)‖ :=
        mul_le_mul_of_nonneg_right hb hc
    _ = Cf i j * ‖TL n (Matrix.single i j 1)‖ * Real.exp (-(d * s)) := by ring
    _ ≤ |Cf i j| * ‖TL n (Matrix.single i j 1)‖ * Real.exp (-(d * s)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hc)
          (Real.exp_pos _).le

/-- shifted coefficients `B_σ(a) = TL S(σ + Re a, Im a) + μ`. -/
noncomputable def Bsh (S : ℝ × ℝ → Mat n) (μ σ : ℝ) (a : ℂ) : Op n :=
  TL n (S (σ + a.re, a.im)) + μ • (1 : Op n)

/-- limit coefficients `B_∞(a) = TL S∞(Im a) + μ`. -/
noncomputable def Binf (Sinf : ℝ → Mat n) (μ : ℝ) (a : ℂ) : Op n :=
  TL n (Sinf a.im) + μ • (1 : Op n)

lemma Bsh_contDiff (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (μ σ : ℝ) : ContDiff ℝ ∞ (Bsh S μ σ) := by
  have h1 : ContDiff ℝ ∞ (fun a : ℂ => ((σ + a.re, a.im) : ℝ × ℝ)) :=
    (contDiff_const.add Complex.reCLM.contDiff).prodMk Complex.imCLM.contDiff
  exact ((contDiff_TL S hS).comp h1).add contDiff_const

lemma Binf_contDiff (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (μ : ℝ) : ContDiff ℝ ∞ (Binf Sinf μ) :=
  ((contDiff_TL1 Sinf hSinf').comp Complex.imCLM.contDiff).add contDiff_const

theorem Bsh_conv (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (d : ℝ) (hd : 0 < d)
    (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d) (μ : ℝ) (σ : ℕ → ℝ)
    (hσ : Tendsto σ atTop atTop) :
    JHolomorphic.TendstoCInftyLocOn (fun ν => Bsh S μ (σ ν)) (Binf Sinf μ) univ := by
  intro K _ hK m
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set eR : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  set c := ‖(eR : ℂ →L[ℝ] ℝ × ℝ)‖ ^ m + 1
  have hc : 0 < c := add_pos_of_nonneg_of_pos (pow_nonneg (norm_nonneg _) m) one_pos
  have hεc : 0 < ε / (2 * c) := div_pos hε (mul_pos two_pos hc)
  obtain ⟨s₁, hs₁⟩ := Dop_decay S hS Sinf hSinf' d hd hSas m (ε / (2 * c)) hεc
  filter_upwards [hσ.eventually_ge_atTop (s₁ + R)] with ν hν a ha
  have haR : ‖a‖ ≤ R := by
    have := hR ha; rwa [Metric.mem_closedBall, dist_zero_right] at this
  set Dop : ℝ × ℝ → Op n := fun p => TL n (S p) - TL n (Sinf p.2)
  have e1 : (Bsh S μ (σ ν) - Binf Sinf μ) = (fun p => Dop (p + (σ ν, 0))) ∘ eR := by
    funext b
    simp only [Pi.sub_apply, Bsh, Binf, Function.comp, Dop, eR,
      Complex.equivRealProdCLM_apply, Prod.mk_add_mk, add_zero, add_comm b.re]
    abel
  rw [dist_eq_norm, norm_sub_rev, ← iteratedFDeriv_sub_apply
    ((Bsh_contDiff S hS μ (σ ν)).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))
    ((Binf_contDiff Sinf hSinf' μ).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))]
  rw [e1]
  refine lt_of_le_of_lt (norm_cle_iter_le eR _ a m) ?_
  rw [iteratedFDeriv_comp_add_right]
  have hre : |a.re| ≤ R := (Complex.abs_re_le_norm a).trans haR
  have hp : s₁ ≤ (eR a + (σ ν, 0)).1 := by
    simp only [eR, Complex.equivRealProdCLM_apply, Prod.fst_add]
    have := neg_abs_le a.re
    linarith only [this, hre, hν]
  have hb := hs₁ _ hp (eR a + (σ ν, 0)).2
  have hpq : ((eR a + (σ ν, 0)).1, (eR a + (σ ν, 0)).2) = eR a + (σ ν, 0) := rfl
  rw [hpq] at hb
  have hn := norm_nonneg (iteratedFDeriv ℝ m Dop (eR a + (σ ν, 0)))
  have hcm : ‖(eR : ℂ →L[ℝ] ℝ × ℝ)‖ ^ m ≤ c := by
    simp only [c]; exact le_add_of_nonneg_right zero_le_one
  calc ‖iteratedFDeriv ℝ m Dop (eR a + (σ ν, 0))‖ * ‖(eR : ℂ →L[ℝ] ℝ × ℝ)‖ ^ m
      ≤ (ε / (2 * c)) * c := mul_le_mul hb hcm (pow_nonneg (norm_nonneg _) m) hεc.le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (mul_pos two_pos hc)]
        nlinarith only [hε, hc]

end HDecay

end AF_F3

section AF_F4

/-! Stage F4: the graph map `u(z) = (z + iτ, χ((σ, τ) + z))`. -/

open scoped Topology ContDiff RealInnerProductSpace ENNReal NNReal
open Set Filter CauchyRiemannIndex MeasureTheory Metric

namespace HDecay

variable {n : ℕ}

/-- the graph map -/
noncomputable def ug (χ : ℝ × ℝ → Vec n) (σ τ : ℝ) (z : ℂ) : ℂ × Vec n :=
  (z + (τ : ℂ) * Complex.I, χ ((σ, τ) + Complex.equivRealProdCLM z))

lemma eR_re_pos {σ τ : ℝ} (hσ : 1 ≤ σ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ((σ, τ) + Complex.equivRealProdCLM z) ∈ Ω := by
  have h1 : |z.re| < 1 := (Complex.abs_re_le_norm z).trans_lt (by simpa using hz)
  refine ⟨?_, mem_univ _⟩
  simp only [Complex.equivRealProdCLM_apply, Prod.fst_add, mem_Ioi]
  have := neg_abs_le z.re
  linarith

lemma ug_hasFDerivAt {χ : ℝ × ℝ → Vec n} (hχ : Sm χ) {σ τ : ℝ} {z : ℂ}
    (hz : ((σ, τ) + Complex.equivRealProdCLM z) ∈ Ω) :
    HasFDerivAt (ug χ σ τ) ((ContinuousLinearMap.id ℝ ℂ).prod
      ((fderiv ℝ χ ((σ, τ) + Complex.equivRealProdCLM z)).comp
        (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ))) z := by
  have h1 : HasFDerivAt (fun z : ℂ => z + (τ : ℂ) * Complex.I) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).add_const _
  have h2 : HasFDerivAt (fun z : ℂ => (σ, τ) + Complex.equivRealProdCLM z)
      (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ) z :=
    (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).hasFDerivAt.const_add _
  exact h1.prodMk ((hχ.diffAt hz).hasFDerivAt.comp z h2)

lemma ug_contDiffOn {χ : ℝ × ℝ → Vec n} (hχ : Sm χ) {σ τ : ℝ} (hσ : 1 ≤ σ) :
    ContDiffOn ℝ ∞ (ug χ σ τ) (ball 0 1) := by
  have h2 : ContDiff ℝ ∞ (fun z : ℂ => (σ, τ) + Complex.equivRealProdCLM z) :=
    contDiff_const.add (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).contDiff
  exact (contDiff_id.add contDiff_const).contDiffOn.prodMk
    (hχ.comp h2.contDiffOn fun z hz => eR_re_pos hσ hz)

lemma ug_fderiv_one {χ : ℝ × ℝ → Vec n} (hχ : Sm χ) {σ τ : ℝ} {z : ℂ}
    (hz : ((σ, τ) + Complex.equivRealProdCLM z) ∈ Ω) :
    fderiv ℝ (ug χ σ τ) z 1 = (1, pS χ ((σ, τ) + Complex.equivRealProdCLM z)) := by
  rw [(ug_hasFDerivAt hχ hz).fderiv]
  simp [pS]

lemma ug_fderiv_I {χ : ℝ × ℝ → Vec n} (hχ : Sm χ) {σ τ : ℝ} {z : ℂ}
    (hz : ((σ, τ) + Complex.equivRealProdCLM z) ∈ Ω) :
    fderiv ℝ (ug χ σ τ) z Complex.I = (Complex.I, pT χ ((σ, τ) + Complex.equivRealProdCLM z)) := by
  rw [(ug_hasFDerivAt hχ hz).fderiv]
  simp [pT]

lemma ug_hol (S : ℝ × ℝ → Mat n) (μ : ℝ) {χ : ℝ × ℝ → Vec n} (hχ : Sm χ)
    (heq : ∀ x ∈ Ω, pS χ x + Jop n (pT χ x) + TL n (S x) (χ x) + μ • χ x = 0)
    {σ τ : ℝ} (hσ : 1 ≤ σ) :
    JHolomorphic.IsJHolomorphicOn (Jof (Bsh S μ σ)) (ball 0 1) (ug χ σ τ) := by
  intro z hz
  have hx := eR_re_pos (τ := τ) hσ hz
  refine ⟨(ug_hasFDerivAt hχ hx).differentiableAt, ?_⟩
  simp only [JHolomorphic.dbarJ]
  rw [ug_fderiv_one hχ hx, ug_fderiv_I hχ hx, Jof_apply]
  have e1 : (ug χ σ τ z).1 = z + (τ : ℂ) * Complex.I := rfl
  have e2 : (ug χ σ τ z).2 = χ ((σ, τ) + Complex.equivRealProdCLM z) := rfl
  have e3 : Bsh S μ σ (z + (τ : ℂ) * Complex.I) =
      TL n (S ((σ, τ) + Complex.equivRealProdCLM z)) + μ • (1 : Op n) := by
    simp only [Bsh, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
      Complex.equivRealProdCLM_apply, Prod.mk_add_mk]
    congr 3 <;> ring
  rw [e1, e2, e3]
  have h := heq _ hx
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Complex.I_re, Complex.I_im, zero_smul, one_smul, zero_add, Prod.snd_add,
      Prod.snd_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    rw [← h]; abel

lemma ug_mapsTo {χ : ℝ × ℝ → Vec n} {s6 M : ℝ}
    (hM : ∀ s ≥ s6, ∀ t, ‖χ (s, t)‖ ≤ M) {σ τ : ℝ} (hσ : s6 + 1 ≤ σ) (hτ : |τ| ≤ 1) :
    MapsTo (ug χ σ τ) (ball 0 1) (closedBall 0 2 ×ˢ closedBall 0 M) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  refine ⟨?_, ?_⟩
  · simp only [ug, mem_closedBall, dist_zero_right]
    calc ‖z + (τ : ℂ) * Complex.I‖ ≤ ‖z‖ + ‖(τ : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ 2 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; linarith
  · simp only [ug, mem_closedBall, dist_zero_right]
    have h1 : |z.re| < 1 := (Complex.abs_re_le_norm z).trans_lt hz1
    have := hM ((σ, τ) + Complex.equivRealProdCLM z).1 (by
      simp only [Complex.equivRealProdCLM_apply, Prod.fst_add]
      have := neg_abs_le z.re; linarith) ((σ, τ) + Complex.equivRealProdCLM z).2
    simpa using this

lemma clm_prod_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℝ × ℝ →L[ℝ] F) :
    ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ⟨a, b⟩ => ?_
  have e : L (a, b) = a • L (1, 0) + b • L (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]; simp
  rw [e]
  have ha : |a| ≤ ‖(a, b)‖ := by simpa using norm_fst_le (a, b)
  have hb : |b| ≤ ‖(a, b)‖ := by simpa using norm_snd_le (a, b)
  calc ‖a • L (1, 0) + b • L (0, 1)‖ ≤ |a| * ‖L (1, 0)‖ + |b| * ‖L (0, 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖(a, b)‖ * ‖L (1, 0)‖ + ‖(a, b)‖ * ‖L (0, 1)‖ := by gcongr
    _ = _ := by ring

lemma eLp_ball_le {F : Type*} [NormedAddCommGroup F] (f : ℂ → F) {B : ℝ}
    (hf : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ B) :
    eLpNorm f (ENNReal.ofReal 3) (volume.restrict (ball 0 1)) ≤
      volume (ball (0 : ℂ) 1) ^ (3 : ℝ)⁻¹ * ENNReal.ofReal B := by
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (ball (0 : ℂ) 1))
    (p := ENNReal.ofReal 3) ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall hf))
  simpa [Measure.restrict_apply_univ, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3)] using h

lemma ug_sobolev {χ : ℝ × ℝ → Vec n} (hχ : Sm χ) {s6 M : ℝ}
    (hM : ∀ s ≥ s6, ∀ t, ‖χ (s, t)‖ ≤ M ∧ ‖pS χ (s, t)‖ ≤ M ∧ ‖pT χ (s, t)‖ ≤ M)
    (hs6 : 0 ≤ s6) :
    ∃ C : ℝ≥0, ∀ σ τ : ℝ, s6 + 1 ≤ σ → |τ| ≤ 1 →
      DbarRegularity.sobolevNorm 1 (ENNReal.ofReal 3) (ball 0 1) (ug χ σ τ) ≤ C := by
  set eR : ℂ →L[ℝ] ℝ × ℝ := (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)
  set V := volume (ball (0 : ℂ) 1) ^ (3 : ℝ)⁻¹
  have hV : V ≠ ⊤ := by
    have : volume (ball (0 : ℂ) 1) ≠ ⊤ := measure_ball_lt_top.ne
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) this
  set B0 := 2 + |M|
  set B1 := 1 + 2 * |M| * ‖eR‖
  refine ⟨(V * ENNReal.ofReal B0 + V * ENNReal.ofReal B1).toNNReal, fun σ τ hσ hτ => ?_⟩
  rw [ENNReal.coe_toNNReal (by
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hV ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top hV ENNReal.ofReal_ne_top⟩)]
  have hσ1 : 1 ≤ σ := by linarith
  have hs : ∀ z ∈ ball (0 : ℂ) 1, s6 ≤ ((σ, τ) + Complex.equivRealProdCLM z).1 := by
    intro z hz
    have h1 : |z.re| < 1 := (Complex.abs_re_le_norm z).trans_lt (by simpa using hz)
    simp only [Complex.equivRealProdCLM_apply, Prod.fst_add]
    have := neg_abs_le z.re; linarith
  simp only [DbarRegularity.sobolevNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  gcongr
  · refine eLp_ball_le _ fun z hz => ?_
    rw [norm_iteratedFDeriv_zero]
    have hmap := ug_mapsTo (fun s hs t => (hM s hs t).1) (by linarith : s6 + 1 ≤ σ) hτ hz
    obtain ⟨h1, h2⟩ := hmap
    rw [mem_closedBall, dist_zero_right] at h1 h2
    calc ‖ug χ σ τ z‖ ≤ ‖(ug χ σ τ z).1‖ + ‖(ug χ σ τ z).2‖ := by
          rw [Prod.norm_def]; exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
      _ ≤ 2 + |M| := by linarith [le_abs_self M]
  · refine eLp_ball_le _ fun z hz => ?_
    have hx := eR_re_pos (τ := τ) hσ1 hz
    rw [norm_iteratedFDeriv_one, (ug_hasFDerivAt hχ hx).fderiv, ContinuousLinearMap.opNorm_prod,
      Prod.norm_def]
    set p := (σ, τ) + Complex.equivRealProdCLM z
    have hp : p = (p.1, p.2) := rfl
    have hb := hM p.1 (hs z hz) p.2
    rw [← hp] at hb
    have hD : ‖fderiv ℝ χ p‖ ≤ 2 * |M| := by
      refine (clm_prod_bound _).trans ?_
      have e1 : fderiv ℝ χ p (1, 0) = pS χ p := rfl
      have e2 : fderiv ℝ χ p (0, 1) = pT χ p := rfl
      rw [e1, e2]; linarith [le_abs_self M]
    have hc : ‖(fderiv ℝ χ p).comp eR‖ ≤ 2 * |M| * ‖eR‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
    have hid : ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    refine max_le (by nlinarith [norm_nonneg eR, abs_nonneg M]) (by linarith)

end HDecay

end AF_F4

section AF_F5

/-! Stage F5: uniform bounds on all derivatives of `χ` (elliptic regularity via the graph trick). -/

open scoped Topology ContDiff RealInnerProductSpace ENNReal NNReal
open Set Filter CauchyRiemannIndex MeasureTheory Metric

namespace HDecay

variable {n : ℕ}

lemma iter_per {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {χ : ℝ × ℝ → F}
    (hper : TPer χ) (m : ℕ) (s t : ℝ) :
    iteratedFDeriv ℝ m χ (s, t) = iteratedFDeriv ℝ m χ (s, Int.fract t) := by
  have hk : ∀ p : ℝ × ℝ, χ (p + (0, ((-⌊t⌋ : ℤ) : ℝ))) = χ p := by
    rintro ⟨a, b⟩
    have := (hper.periodic a).int_mul (-⌊t⌋) b
    simpa using this
  have e : χ = fun p => χ (p + (0, ((-⌊t⌋ : ℤ) : ℝ))) := funext fun p => (hk p).symm
  conv_lhs => rw [e]
  rw [iteratedFDeriv_comp_add_right]
  congr 1
  simp [Int.fract, sub_eq_add_neg]

lemma iter_chi_le_ug {χ : ℝ × ℝ → Vec n} (hχ : Sm χ) {σ τ : ℝ} (hσ : 1 ≤ σ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m χ (σ, τ)‖ ≤
      ‖iteratedFDeriv ℝ m (ug χ σ τ) 0‖ *
        ‖((Complex.equivRealProdCLM.symm : (ℝ × ℝ) ≃L[ℝ] ℂ) : (ℝ × ℝ) →L[ℝ] ℂ)‖ ^ m := by
  set eS : (ℝ × ℝ) ≃L[ℝ] ℂ := Complex.equivRealProdCLM.symm
  set g : ℂ → Vec n := Prod.snd ∘ ug χ σ τ
  have e1 : (fun p => χ (p + (σ, τ))) = g ∘ eS := by
    funext p
    simp only [g, eS, Function.comp, ug, ContinuousLinearEquiv.apply_symm_apply, add_comm p]
  have h1 : iteratedFDeriv ℝ m χ (σ, τ) = iteratedFDeriv ℝ m (fun p => χ (p + (σ, τ))) 0 := by
    rw [iteratedFDeriv_comp_add_right, zero_add]
  rw [h1, e1]
  refine (norm_cle_iter_le eS g 0 m).trans ?_
  rw [map_zero]
  gcongr
  have hc : ContDiffAt ℝ ∞ (ug χ σ τ) 0 :=
    (ug_contDiffOn hχ (τ := τ) hσ).contDiffAt (ball_mem_nhds 0 one_pos)
  have := (ContinuousLinearMap.snd ℝ ℂ (Vec n)).norm_iteratedFDeriv_comp_left hc
    (n := m) (by exact_mod_cast le_top)
  refine this.trans ?_
  have hs := ContinuousLinearMap.norm_snd_le ℝ ℂ (Vec n)
  have := norm_nonneg (iteratedFDeriv ℝ m (ug χ σ τ) 0)
  nlinarith

theorem deriv_bounds (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (d : ℝ) (hd : 0 < d)
    (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d) (μ : ℝ)
    {χ : ℝ × ℝ → Vec n} (hχ : Sm χ) (hper : TPer χ)
    (heq : ∀ x ∈ Ω, pS χ x + Jop n (pT χ x) + TL n (S x) (χ x) + μ • χ x = 0)
    {s6 M : ℝ} (hs6 : 0 ≤ s6)
    (hM : ∀ s ≥ s6, ∀ t, ‖χ (s, t)‖ ≤ M ∧ ‖pS χ (s, t)‖ ≤ M ∧ ‖pT χ (s, t)‖ ≤ M) (m : ℕ) :
    ∃ Mm s', ∀ s ≥ s', ∀ t, ‖iteratedFDeriv ℝ m χ (s, t)‖ ≤ Mm := by
  by_contra hcon
  push Not at hcon
  have h' : ∀ ν : ℕ, ∃ s, (ν : ℝ) + s6 + 1 ≤ s ∧ ∃ t, (ν : ℝ) < ‖iteratedFDeriv ℝ m χ (s, t)‖ :=
    fun ν => by
      obtain ⟨s, hs, t, ht⟩ := hcon ν ((ν : ℝ) + s6 + 1)
      exact ⟨s, hs, t, ht⟩
  choose σ hσ tf htf using h'
  set τ : ℕ → ℝ := fun ν => Int.fract (tf ν)
  have hτ : ∀ ν, |τ ν| ≤ 1 := fun ν => by
    rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
  have hσ1 : ∀ ν, s6 + 1 ≤ σ ν := fun ν => by
    have := hσ ν; have : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν; linarith
  have hσt : Tendsto σ atTop atTop := by
    refine tendsto_atTop_mono (fun ν => ?_) tendsto_natCast_atTop_atTop
    have := hσ ν; linarith
  have hJ := Jof_conv (fun ν => Bsh_contDiff S hS μ (σ ν)) (Binf_contDiff Sinf hSinf' μ)
    (Bsh_conv S hS Sinf hSinf' d hd hSas μ σ hσt)
  obtain ⟨C, hC⟩ := ug_sobolev hχ hM hs6
  have hK₀ : IsCompact (closedBall (0 : ℂ) 2 ×ˢ closedBall (0 : Vec n) M) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hB := JHolomorphic.bounded_iteratedFDeriv_of_sobolevNorm_le 3 (by norm_num)
    (Jof (Binf Sinf μ)) (fun ν => Jof (Bsh S μ (σ ν))) univ _
    (Jof_almostComplex (Binf_contDiff Sinf hSinf' μ))
    (fun ν => Jof_almostComplex (Bsh_contDiff S hS μ (σ ν))) hJ hK₀ (subset_univ _)
    (fun ν => ug χ (σ ν) (τ ν))
    (fun ν => ug_contDiffOn hχ (by linarith [hσ1 ν]))
    (fun ν => ug_hol S μ hχ heq (by linarith [hσ1 ν]))
    (fun ν => ug_mapsTo (fun s hs t => (hM s hs t).1) (hσ1 ν) (hτ ν)) C
    (fun ν => hC (σ ν) (τ ν) (hσ1 ν) (hτ ν))
    {0} (by simp) isCompact_singleton m
  obtain ⟨Mb, hMb⟩ := hB
  set q := ‖((Complex.equivRealProdCLM.symm : (ℝ × ℝ) ≃L[ℝ] ℂ) : (ℝ × ℝ) →L[ℝ] ℂ)‖ ^ m
  obtain ⟨ν, hν⟩ := exists_nat_gt (|Mb| * q)
  have h1 := iter_chi_le_ug hχ (σ := σ ν) (τ := τ ν) (by linarith [hσ1 ν]) m
  have h2 := hMb ν 0 rfl
  have h3 := htf ν
  rw [iter_per hper] at h3
  have hq : 0 ≤ q := by positivity
  have : ‖iteratedFDeriv ℝ m (ug χ (σ ν) (τ ν)) 0‖ * q ≤ |Mb| * q :=
    mul_le_mul_of_nonneg_right (h2.trans (le_abs_self _)) hq
  linarith

end HDecay

end AF_F5

section SP3

/-! Stage F6: interpolation (bounded derivatives + `C⁰` decay ⇒ `C^∞` decay) and assembly. -/

open scoped Topology ContDiff RealInnerProductSpace ENNReal NNReal
open Set Filter CauchyRiemannIndex MeasureTheory Metric

namespace HDecay

/-- Landau-type estimate on `ℝ × ℝ`. -/
lemma landau2 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : ℝ × ℝ → G) (z : ℝ × ℝ)
    {h ε0 M : ℝ} (hh : 0 < h) (hε0 : 0 ≤ ε0) (hM : 0 ≤ M)
    (hd : ∀ x ∈ closedBall z h, DifferentiableAt ℝ g x)
    (hL : ∀ x ∈ closedBall z h, ‖fderiv ℝ g x - fderiv ℝ g z‖ ≤ M * h)
    (hg : ∀ x ∈ closedBall z h, ‖g x‖ ≤ ε0) :
    ‖fderiv ℝ g z‖ ≤ 2 * ε0 / h + M * h := by
  set A := fderiv ℝ g z
  have key : ∀ y ∈ closedBall z h, ‖A (y - z)‖ ≤ 2 * ε0 + M * h * ‖y - z‖ := by
    intro y hy
    have hz : z ∈ closedBall z h := mem_closedBall_self hh.le
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun x => g x - A x) (f' := fun x => fderiv ℝ g x - A)
      (fun x hx => ((hd x hx).hasFDerivAt.sub A.hasFDerivAt).hasFDerivWithinAt)
      (fun x hx => hL x hx) (convex_closedBall z h) hz hy
    have e1 : A (y - z) = (g y - g z) - ((g y - A y) - (g z - A z)) := by
      rw [map_sub]; abel
    rw [e1]
    calc ‖(g y - g z) - ((g y - A y) - (g z - A z))‖
        ≤ ‖g y - g z‖ + ‖(g y - A y) - (g z - A z)‖ := norm_sub_le _ _
      _ ≤ (‖g y‖ + ‖g z‖) + M * h * ‖y - z‖ := add_le_add (norm_sub_le _ _) hmv
      _ ≤ 2 * ε0 + M * h * ‖y - z‖ := by linarith [hg y hy, hg z hz]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set y := z + (h / ‖x‖) • x
  have hyz : y - z = (h / ‖x‖) • x := by simp [y]
  have hny : ‖y - z‖ = h := by
    rw [hyz, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hy : y ∈ closedBall z h := by rw [mem_closedBall, dist_eq_norm, hny]
  have k := key y hy
  rw [hny, hyz, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at k
  have : ‖A x‖ = (‖x‖ / h) * ((h / ‖x‖) * ‖A x‖) := by field_simp
  rw [this]
  calc (‖x‖ / h) * ((h / ‖x‖) * ‖A x‖) ≤ (‖x‖ / h) * (2 * ε0 + M * h * h) :=
        mul_le_mul_of_nonneg_left k (by positivity)
    _ = (2 * ε0 / h + M * h) * ‖x‖ := by field_simp

theorem interp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × ℝ → F) (s0 : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioi s0 ×ˢ univ))
    (hb : ∀ m : ℕ, ∃ B s', ∀ s ≥ s', ∀ t, ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ B)
    (h0 : ∀ ε > 0, ∃ s₁, ∀ s ≥ s₁, ∀ t, ‖f (s, t)‖ ≤ ε) :
    ∀ m : ℕ, ∀ ε > 0, ∃ s₁, ∀ s ≥ s₁, ∀ t, ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ ε := by
  intro m
  induction m with
  | zero =>
    intro ε hε
    obtain ⟨s₁, h⟩ := h0 ε hε
    exact ⟨s₁, fun s hs t => by rw [norm_iteratedFDeriv_zero]; exact h s hs t⟩
  | succ m ih =>
    intro ε hε
    obtain ⟨B, sB, hB⟩ := hb (m + 2)
    set B' := |B| + 1
    have hB' : 0 < B' := by positivity
    set h := min 1 (ε / (2 * B'))
    have hh : 0 < h := lt_min one_pos (by positivity)
    have hh1 : h ≤ 1 := min_le_left _ _
    have hh2 : h ≤ ε / (2 * B') := min_le_right _ _
    set ε0 := ε * h / 4
    have hε0 : 0 < ε0 := by positivity
    obtain ⟨s₁, hs₁⟩ := ih ε0 hε0
    set R := max (max s₁ sB) s0
    refine ⟨R + 2, fun s hs t => ?_⟩
    set z : ℝ × ℝ := (s, t)
    have hreg : ∀ x ∈ closedBall z h, R + 1 ≤ x.1 := by
      intro x hx
      have h1 : ‖x - z‖ ≤ h := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
      have h2 : |x.1 - s| ≤ h := by
        have := norm_fst_le (x - z)
        simp only [Prod.fst_sub, Real.norm_eq_abs, z] at this
        linarith
      have := neg_abs_le (x.1 - s)
      linarith
    have hopen : IsOpen (Ioi s0 ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hcd : ∀ x ∈ closedBall z h, ContDiffAt ℝ ∞ f x := fun x hx =>
      hf.contDiffAt (hopen.mem_nhds ⟨by
        have := hreg x hx
        show s0 < x.1
        have : s0 ≤ R := le_max_right _ _
        linarith, mem_univ _⟩)
    have hdiff : ∀ k : ℕ, ∀ x ∈ closedBall z h, DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      fun k x hx => ((hcd x hx).iteratedFDeriv_right (m := 1) (i := k)
        (by exact_mod_cast le_top)).differentiableAt one_ne_zero
    have hfd : ∀ x ∈ closedBall z h, ‖fderiv ℝ (iteratedFDeriv ℝ (m + 1) f) x‖ ≤ |B| := by
      intro x hx
      rw [norm_fderiv_iteratedFDeriv]
      have : sB ≤ x.1 := by
        have := hreg x hx
        have : sB ≤ R := (le_max_right _ _).trans (le_max_left _ _)
        linarith
      exact (hB x.1 this x.2).trans (le_abs_self _)
    have e : ∀ y, fderiv ℝ (iteratedFDeriv ℝ m f) y =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => ℝ × ℝ) F)
          (iteratedFDeriv ℝ (m + 1) f y) := by
      intro y; rw [iteratedFDeriv_succ_eq_comp_left]; simp
    have hL : ∀ x ∈ closedBall z h, ‖fderiv ℝ (iteratedFDeriv ℝ m f) x -
        fderiv ℝ (iteratedFDeriv ℝ m f) z‖ ≤ |B| * h := by
      intro x hx
      rw [e x, e z, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (hdiff (m + 1)) hfd
        (convex_closedBall z h) (mem_closedBall_self hh.le) hx
      refine this.trans ?_
      gcongr
      rw [← dist_eq_norm]; exact mem_closedBall.1 hx
    have hg : ∀ x ∈ closedBall z h, ‖iteratedFDeriv ℝ m f x‖ ≤ ε0 := by
      intro x hx
      have : s₁ ≤ x.1 := by
        have := hreg x hx
        have : s₁ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
        linarith
      exact hs₁ x.1 this x.2
    have hla := landau2 (iteratedFDeriv ℝ m f) z hh hε0.le (abs_nonneg B) (hdiff m) hL hg
    rw [← norm_fderiv_iteratedFDeriv]
    refine hla.trans ?_
    have e1 : 2 * ε0 / h = ε / 2 := by simp only [ε0]; field_simp; ring
    have e2 : |B| * h ≤ ε / 2 := by
      calc |B| * h ≤ B' * (ε / (2 * B')) := by
            gcongr
            simp only [B']; linarith
        _ = ε / 2 := by field_simp
    linarith

variable {n : ℕ}

lemma per_iter_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (e : ℝ → F)
    (he : ContDiff ℝ ∞ e) (hp : Function.Periodic e 1) (m : ℕ) :
    ∃ B, ∀ t, ‖iteratedFDeriv ℝ m e t‖ ≤ B := by
  have hc : Continuous (iteratedFDeriv ℝ m e) :=
    he.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hc.continuousOn
  refine ⟨B, fun t => ?_⟩
  have hk : e = fun x => e (x + ((-⌊t⌋ : ℤ) : ℝ)) := by
    funext x
    have := hp.int_mul (-⌊t⌋) x
    simpa using this.symm
  have : iteratedFDeriv ℝ m e t = iteratedFDeriv ℝ m e (Int.fract t) := by
    conv_lhs => rw [hk]
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    simp [Int.fract, sub_eq_add_neg]
  rw [this]
  exact hB _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

lemma snd_iter_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (e : ℝ → F)
    (he : ContDiff ℝ ∞ e) (m : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => e p.2) x‖ ≤ ‖iteratedFDeriv ℝ m e x.2‖ := by
  have e1 : (fun p : ℝ × ℝ => e p.2) = e ∘ (ContinuousLinearMap.snd ℝ ℝ ℝ) := rfl
  rw [e1, (ContinuousLinearMap.snd ℝ ℝ ℝ).iteratedFDeriv_comp_right he x
    (by exact_mod_cast le_top)]
  refine ((iteratedFDeriv ℝ m e _).norm_compContinuousLinearMap_le _).trans ?_
  have hp : ∏ _i : Fin m, ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_snd_le _ _ _
  have := norm_nonneg (iteratedFDeriv ℝ m e x.2)
  simp only [ContinuousLinearMap.coe_snd'] at hp ⊢
  nlinarith

set_option maxHeartbeats 1000000 in
theorem final_formula (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ e : ℝ → Vec n, FiniteEnergyPlane.IsLoopEigen Sinf μ e ∧
      FiniteEnergyPlane.TendstoZeroCInfty
        (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p - e p.2) := by
  obtain ⟨μ, hμ, e, he, s6, hs6, M, b, Cc, hb, hbd⟩ :
      ∃ μ, μ ≤ δ₀ ∧ ∃ e : ℝ → Vec n, FiniteEnergyPlane.IsLoopEigen Sinf μ e ∧
        ∃ s6 > 0, ∃ M b Cc : ℝ, 0 < b ∧ ∀ s ≥ s6, ∀ t,
          ‖χr ζ μ (s, t) - e t‖ ≤ Cc * Real.exp (-(b * s)) ∧ ‖χr ζ μ (s, t)‖ ≤ M ∧
          ‖pS (χr ζ μ) (s, t)‖ ≤ M ∧ ‖pT (χr ζ μ) (s, t)‖ ≤ M :=
    FiniteEnergyPlane.halfCyl_rescaled_exp_conv S hS hSper Sinf hSinf hSinf' d hd hSas ζ hζ hne C δ₀
      hgrowth
  refine ⟨μ, hμ, e, he, ?_⟩
  set χ := χr ζ μ
  have hfun : (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p - e p.2) =
      fun p => χ p - e p.2 := rfl
  rw [hfun]
  have hζs : Sm ζ := hζ.1
  have hχ : Sm χ := hζs.χr μ
  have hper : TPer χ := TPer.χr hζ.2.1 μ
  have he' : ContDiff ℝ ∞ (fun p : ℝ × ℝ => e p.2) := he.1.comp contDiff_snd
  have hsm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => χ p - e p.2) (Ioi 0 ×ˢ univ) :=
    ContDiffOn.sub hχ he'.contDiffOn
  set A : ℝ × ℝ → Op n := fun p => TL n (S p)
  have hres0 : ∀ x ∈ Ω, res A ζ x = 0 := by
    rintro ⟨a, b⟩ hx
    exact hζ.2.2 a hx.1 b
  have heq : ∀ x ∈ Ω, pS χ x + Jop n (pT χ x) + TL n (S x) (χ x) + μ • χ x = 0 := by
    rintro ⟨s, t⟩ hx
    have h := χr_eq hζs hres0 Sinf μ hx.1 t
    rw [ContinuousLinearMap.sub_apply] at h
    calc pS χ (s, t) + Jop n (pT χ (s, t)) + TL n (S (s, t)) (χ (s, t)) + μ • χ (s, t)
        = -((-(Jop n (pT (χr ζ μ) (s, t))) - TL n (Sinf t) (χr ζ μ (s, t)) - μ • χr ζ μ (s, t)) -
          (pS (χr ζ μ) (s, t) + (A (s, t) (χr ζ μ (s, t)) - TL n (Sinf t) (χr ζ μ (s, t))))) := by
          simp only [A, χ]; abel
      _ = 0 := by rw [h, sub_self, neg_zero]
  have hM : ∀ s ≥ s6, ∀ t, ‖χ (s, t)‖ ≤ M ∧ ‖pS χ (s, t)‖ ≤ M ∧ ‖pT χ (s, t)‖ ≤ M :=
    fun s hs t => (hbd s hs t).2
  refine ⟨⟨0, hsm⟩, interp _ 0 hsm ?_ ?_⟩
  · intro m
    obtain ⟨Mm, s', hMm⟩ := deriv_bounds S hS Sinf hSinf' d hd hSas μ hχ hper heq hs6.le hM m
    obtain ⟨Be, hBe⟩ := per_iter_bound e he.1 he.2.1 m
    refine ⟨Mm + Be, max s' 1, fun s hs t => ?_⟩
    have hx : (s, t) ∈ Ω := mem_Ω (by linarith [le_max_right s' 1])
    have hc1 : ContDiffAt ℝ ∞ χ (s, t) := hχ.contDiffAt (isOpen_Ω.mem_nhds hx)
    have e1 : (fun p : ℝ × ℝ => χ p - e p.2) = χ - fun p : ℝ × ℝ => e p.2 := rfl
    rw [e1, iteratedFDeriv_sub_apply (hc1.of_le (by exact_mod_cast le_top))
      (he'.contDiffAt.of_le (by exact_mod_cast le_top))]
    refine (norm_sub_le _ _).trans (add_le_add (hMm s (le_of_max_le_left hs) t) ?_)
    exact (snd_iter_bound e he.1 m (s, t)).trans (hBe t)
  · intro ε hε
    have ht : Tendsto (fun s => Cc * Real.exp (-(b * s))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => b * s) atTop atTop := tendsto_id.const_mul_atTop hb
      have : Tendsto (fun s => Real.exp (-(b * s))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      simpa using this.const_mul Cc
    obtain ⟨s2, hs2⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds hε))
    exact ⟨max s6 s2, fun s hs t =>
      ((hbd s (le_of_max_le_left hs) t).1).trans (hs2 s (le_of_max_le_right hs))⟩

end HDecay

theorem solution {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, FiniteEnergyPlane.IsLoopEigen Sinf μ e ∧
      FiniteEnergyPlane.TendstoZeroCInfty
        (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p - e p.2) :=
  HDecay.final_formula S hS hSper Sinf hSinf hSinf' d hd hSas ζ hζ hne C δ₀ hgrowth

end SP3
