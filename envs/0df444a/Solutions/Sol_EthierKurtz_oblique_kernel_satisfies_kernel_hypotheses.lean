-- Prove2me | solution 1 for EthierKurtz.oblique_kernel_satisfies_kernel_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T16:59:21.747798+00:00
-- url     : https://prove2.me/submissions/c7aff644-7f07-4e09-9388-73ad341da8b8

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_heat_kernel_solves_heat_equation
import Theorems.Thm_EthierKurtz_ray_kernel_derivative_bounds
import Theorems.Thm_EthierKurtz_ray_kernel_heat_equation_and_mass
import Theorems.Thm_EthierKurtz_ray_kernel_smoothness_and_mass
import Theorems.Thm_EthierKurtz_oblique_kernel_bounds_heat_mass
import Theorems.Thm_EthierKurtz_oblique_kernel_domination

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

/-- Shortcut instances: without them `Norm (E →L E →L E →L ℝ)` fails to synthesize. -/
noncomputable local instance instL2N (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL1N (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL1S (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance instL1C (d : ℕ) : CompleteSpace (Eu d →L[ℝ] ℝ) := inferInstance

local instance instL2C (d : ℕ) : CompleteSpace (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance

local instance instEC (d : ℕ) : CompleteSpace (Eu d) := inferInstance

noncomputable local instance instL3N (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance instL3C (d : ℕ) : CompleteSpace (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance

local instance instL1M (d : ℕ) : ContinuousSMul ℝ (Eu d →L[ℝ] ℝ) := inferInstance

local instance instL2M (d : ℕ) : ContinuousSMul ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance

local instance instENI (d : ℕ) : (volume : Measure (Eu d)).IsNegInvariant := inferInstance

local instance instEMN (d : ℕ) : MeasurableNeg (Eu d) := inferInstance

/-- Hypotheses on a kernel family `K t x y` (time `t > 0`) with `x`-derivatives `K1 K2 K3`
and Gaussian bounds on the convex set `S`. -/
structure KHyp (d : ℕ) (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ)
    (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ))
    (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)) (A c : ℝ) : Prop where
  hA : 0 ≤ A
  hc : 0 < c
  hS : MeasurableSet S
  hconv : Convex ℝ S
  d1 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K t x y) (K1 t x y) x
  d2 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x
  d3 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x
  b0 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y)
  b1 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y)
  b2 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y)
  b3 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G d (c * t) (x - y)
  m0 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K p.1 x p.2)
  m1 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K1 p.1 x p.2)
  m2 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K2 p.1 x p.2)
  m3 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2)
  dom : ∀ t, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, IntegrableOn F S ∧
    ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧
      ‖K2 t x y‖ ≤ F y ∧ ‖K3 t x y‖ ≤ F y
  heat : ∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => K t x y)
    ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t
  mass : ∀ t, 0 < t → ∀ x, ∫ y in S, K t x y = 1

section KernelInt

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}

variable {h : Eu d → ℝ} {M0 : ℝ}

end KernelInt

section KernelBounds

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

end KernelBounds

section TimeK

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

variable {lam : ℝ}

end TimeK

section TimeHol

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

end TimeHol

section TimeDeriv

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

end TimeDeriv

section TimeEq

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

end TimeEq

section GDeriv

variable {d : ℕ}

noncomputable local instance instL2N' (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S' (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The real inner product as a continuous bilinear map. -/
noncomputable def Ip (d : ℕ) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ := innerSL ℝ

noncomputable def ge (d : ℕ) (a : ℝ) (z : Eu d) : ℝ := rexp (-(a * ‖z‖ ^ 2))

noncomputable def gK1 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] ℝ := (-(2 * a) * ge d a z) • Ip d z

noncomputable def gK2 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ge d a z • ((4 * a ^ 2) • (Ip d z).smulRight (Ip d z) - (2 * a) • Ip d)

noncomputable def gK3 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  fderiv ℝ (gK2 a) z

end GDeriv

section Whole

variable {d : ℕ}

noncomputable local instance instL2N5 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S5 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Normalisation of the heat kernel at time `t`. -/
noncomputable def hN (d : ℕ) (t : ℝ) : ℝ := (π * (2 * t)) ^ (-((d : ℝ) / 2))

noncomputable def wK (d : ℕ) (t : ℝ) (x y : Eu d) : ℝ := G d (2 * t) (x - y)

noncomputable def wK1 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] ℝ := hN d t • gK1 (1 / (2 * t)) (x - y)

noncomputable def wK2 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • gK2 (1 / (2 * t)) (x - y)

noncomputable def wK3 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • gK3 (1 / (2 * t)) (x - y)

/-- The constant of the whole-space kernel bounds. -/
noncomputable def wA (d : ℕ) : ℝ := 51 * 2 ^ ((d : ℝ) / 2)

end Whole

section Whole2

variable {d : ℕ}

noncomputable local instance instL2N6 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S6 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end Whole2

section HalfGeom

variable {d : ℕ}

/-- Reflection across the hyperplane `⟪x, e⟫ = 0`. -/
noncomputable def Rf (e x : Eu d) : Eu d := x - (2 * inner ℝ x e) • e

/-- The constant of the ray lower bound. -/
noncomputable def rK (b : Eu d) : ℝ := 14 + 8 * ‖b‖ ^ 2

end HalfGeom

section GDeriv4

variable {d : ℕ}

noncomputable local instance instL2N7 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S7 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N7 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S7 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def gK4 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  fderiv ℝ (gK3 a) z

end GDeriv4

section GDeriv4b

variable {d : ℕ}

noncomputable local instance instL2N7b (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S7b (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N7b (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S7b (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def eb1 (b : Eu d) : (Eu d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ b

noncomputable def eb2 (b : Eu d) : (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] (Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.compL ℝ (Eu d) (Eu d →L[ℝ] ℝ) ℝ (eb1 b)

noncomputable def eb3 (b : Eu d) :
    (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.compL ℝ (Eu d) (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (Eu d →L[ℝ] ℝ) (eb2 b)

noncomputable def rP0 (b : Eu d) (t : ℝ) (w : Eu d) : ℝ := hN d t * eb1 b (gK1 (1 / (2 * t)) w)

noncomputable def rP1 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] ℝ :=
  hN d t • eb2 b (gK2 (1 / (2 * t)) w)

noncomputable def rP2 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • eb3 b (gK3 (1 / (2 * t)) w)

noncomputable def rP3 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • (eb3 b).comp (gK4 (1 / (2 * t)) w)

end GDeriv4b

section RayK

variable {d : ℕ}

noncomputable local instance instL2N8 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S8 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N8 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S8 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def rk0 (e b : Eu d) (t : ℝ) (x y : Eu d) : ℝ :=
  ∫ s in Ioi (0 : ℝ), rP0 b t (x - Rf e y + s • (e - b))

noncomputable def rk1 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] ℝ :=
  ∫ s in Ioi (0 : ℝ), rP1 b t (x - Rf e y + s • (e - b))

noncomputable def rk2 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ s in Ioi (0 : ℝ), rP2 b t (x - Rf e y + s • (e - b))

noncomputable def rk3 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ s in Ioi (0 : ℝ), rP3 b t (x - Rf e y + s • (e - b))

/-- `rC` at `m = 0`, `σ = 4t`, as a multiple of `√t`. -/
noncomputable def rB (d : ℕ) (b : Eu d) : ℝ := rK b ^ ((d : ℝ) / 2) * (√(π * (rK b * 4)) / 2)

/-- The ray-kernel constant on the half-space. -/
noncomputable def rA (d : ℕ) (b : Eu d) : ℝ := ‖b‖ * (2 * wA d) * rB d b

end RayK

section RayHeat

variable {d : ℕ}

noncomputable local instance instL2N9 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S9 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N9 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S9 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end RayHeat

section Mass

variable {d : ℕ}

noncomputable local instance instL2N10 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S10 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The closed half-space `⟪y, e⟫ ≥ 0`. -/
def Hs (e : Eu d) : Set (Eu d) := {y | 0 ≤ inner ℝ y e}

end Mass

section RayMeas

variable {d : ℕ}

noncomputable local instance instL2N11 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S11 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N11 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S11 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end RayMeas

section OblDomA

variable {d : ℕ}

noncomputable local instance instL2N14 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S14 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N14 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S14 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def oK (e b : Eu d) (t : ℝ) (x y : Eu d) : ℝ :=
  wK d t x y + wK d t x (Rf e y) - 2 * rk0 e b t x y

noncomputable def oK1 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] ℝ :=
  wK1 t x y + wK1 t x (Rf e y) - (2 : ℝ) • rk1 e b t x y

noncomputable def oK2 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  wK2 t x y + wK2 t x (Rf e y) - (2 : ℝ) • rk2 e b t x y

noncomputable def oK3 (e b : Eu d) (t : ℝ) (x y : Eu d) :
    Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  wK3 t x y + wK3 t x (Rf e y) - (2 : ℝ) • rk3 e b t x y

/-- The kernel constant. -/
noncomputable def oA (d : ℕ) (b : Eu d) : ℝ := 2 * wA d * rK b ^ ((d : ℝ) / 2) + 2 * rA d b

end OblDomA

section OblDomB

variable {d : ℕ}

noncomputable local instance instL2N15 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S15 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N15 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S15 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end OblDomB

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  wK_d1 : ∀ (t : ℝ) (x y : Eu d), HasFDerivAt (fun x => wK d t x y) (wK1 t x y) x
  wK_d2 : ∀ (t : ℝ) (x y : Eu d), HasFDerivAt (fun x => wK1 t x y) (wK2 t x y) x
  wK_d3 : ∀ (t : ℝ) (x y : Eu d), HasFDerivAt (fun x => wK2 t x y) (wK3 t x y) x
  whole_meas : ∀ (x : Eu d), StronglyMeasurable (fun p : ℝ × Eu d => wK d p.1 x p.2) ∧ StronglyMeasurable (fun p : ℝ × Eu d => wK1 p.1 x p.2) ∧ StronglyMeasurable (fun p : ℝ × Eu d => wK2 p.1 x p.2) ∧ StronglyMeasurable (fun p : ℝ × Eu d => wK3 p.1 x p.2)
  rK_pos : ∀ (b : Eu d), 0 < rK b
  rk_d0 : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : Eu d), HasFDerivAt (fun x => rk0 e b t x y) (rk1 e b t x y) x
  rk_d1 : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : Eu d), HasFDerivAt (fun x => rk1 e b t x y) (rk2 e b t x y) x
  rk_d2 : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : Eu d), HasFDerivAt (fun x => rk2 e b t x y) (rk3 e b t x y) x
  measurableSet_Hs : ∀ (e : Eu d), MeasurableSet (Hs e)
  continuous_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1), Continuous (Rf e)
  sm_rk0 : ∀ {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d), StronglyMeasurable (fun p : ℝ × Eu d => rk0 e b p.1 x p.2)
  sm_rk1 : ∀ {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d), StronglyMeasurable (fun p : ℝ × Eu d => rk1 e b p.1 x p.2)
  sm_rk2 : ∀ {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d), StronglyMeasurable (fun p : ℝ × Eu d => rk2 e b p.1 x p.2)
  sm_rk3 : ∀ {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d), StronglyMeasurable (fun p : ℝ × Eu d => rk3 e b p.1 x p.2)
  oA_nonneg : ∀ (b : Eu d), 0 ≤ oA d b
  convex_Hs : ∀ (e : Eu d), Convex ℝ (Hs e)
  oK_bounds : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0), (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, |oK e b t x y| ≤ oA d b * G d (rK b * 4 * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK1 e b t x y‖ ≤ oA d b * t ^ (-(1 / 2 : ℝ)) * G d (rK b * 4 * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK2 e b t x y‖ ≤ oA d b * t ^ (-(1 : ℝ)) * G d (rK b * 4 * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK3 e b t x y‖ ≤ oA d b * t ^ (-(3 / 2 : ℝ)) * G d (rK b * 4 * t) (x - y))
  oK_heat : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0), ∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => oK e b t x y) ((1 / 2 : ℝ) * ∑ i, oK2 e b t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t
  oK_mass : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0), ∀ t, 0 < t → ∀ x, ∫ y in Hs e, oK e b t x y = 1
  oK_dom : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0), ∀ t, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, IntegrableOn F (Hs e) ∧ ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Hs e, |oK e b t x y| ≤ F y ∧ ‖oK1 e b t x y‖ ≤ F y ∧ ‖oK2 e b t x y‖ ≤ F y ∧ ‖oK3 e b t x y‖ ≤ F y

end IFk

export IFacts (wK_d1 wK_d2 wK_d3 whole_meas rK_pos rk_d0 rk_d1 rk_d2 measurableSet_Hs continuous_Rf sm_rk0 sm_rk1 sm_rk2 sm_rk3 oA_nonneg convex_Hs oK_bounds oK_heat oK_mass oK_dom)

section PlainK

variable {d : ℕ}

variable [IFacts d]

lemma app3_le {T : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ} {B : ℝ} (h : ‖T‖ ≤ B) (v w z : Eu d) :
    |T v w z| ≤ B * ‖v‖ * ‖w‖ * ‖z‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖T v w z‖ ≤ ‖T v w‖ * ‖z‖ := (T v w).le_opNorm z
    _ ≤ ‖T v‖ * ‖w‖ * ‖z‖ := by gcongr; exact (T v).le_opNorm w
    _ ≤ ‖T‖ * ‖v‖ * ‖w‖ * ‖z‖ := by gcongr; exact T.le_opNorm v
    _ ≤ B * ‖v‖ * ‖w‖ * ‖z‖ := by gcongr

lemma plain_of_khyp {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
    {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
    {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
    (h : KHyp d S K K1 K2 K3 A c) : 0 ≤ A ∧ 0 < c ∧ MeasurableSet (S) ∧ Convex ℝ (S) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ∀ v w z : EuclideanSpace ℝ (Fin d),
        |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K p.1 x p.2)) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K1 p.1 x p.2)) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K2 p.1 x p.2)) ∧
      (∀ x v w z : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K3 p.1 x p.2 v w z)) ∧
      (∀ t : ℝ, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.IntegrableOn F (S) ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ (S), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧
          ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasDerivAt (fun t => K t x y)
        ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
      (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), ∫ y in (S), K t x y = 1) := by
  refine ⟨h.hA, h.hc, h.hS, h.hconv, h.d1, h.d2, h.d3, h.b0, h.b1, h.b2,
    fun t ht x hx y hy v w z => app3_le (h.b3 t ht x hx y hy) v w z, h.m0, h.m1, h.m2,
    fun x v w z => ((ContinuousLinearMap.apply ℝ ℝ z).continuous.comp
      ((ContinuousLinearMap.apply ℝ _ w).continuous.comp
        (ContinuousLinearMap.apply ℝ _ v).continuous)).comp_stronglyMeasurable (h.m3 x),
    fun t ht x₀ => ?_, h.heat, h.mass⟩
  obtain ⟨r, hr, F, hF, hb⟩ := h.dom t ht x₀
  exact ⟨r, hr, F, hF, fun x hx y hy => ⟨(hb x hx y hy).1, (hb x hx y hy).2.1, (hb x hx y hy).2.2.1,
    fun v w z => app3_le (hb x hx y hy).2.2.2 v w z⟩⟩

end PlainK

section Oblique

variable {d : ℕ}

variable [IFacts d]

noncomputable local instance instL2N12 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S12 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N12 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S12 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem obliqueKHyp {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) :
    KHyp d (Hs e) (oK e b) (oK1 e b) (oK2 e b) (oK3 e b) (oA d b) (rK b * 4) where
  hA := oA_nonneg b
  hc := by have := rK_pos b; positivity
  hS := measurableSet_Hs e
  hconv := convex_Hs e
  d1 := fun t ht x y => ((wK_d1 t x y).add (wK_d1 t x (Rf e y))).sub ((rk_d0 he hb ht x y).const_mul 2)
  d2 := fun t ht x y =>
    ((wK_d2 t x y).add (wK_d2 t x (Rf e y))).sub ((rk_d1 he hb ht x y).const_smul (2 : ℝ))
  d3 := fun t ht x y =>
    ((wK_d3 t x y).add (wK_d3 t x (Rf e y))).sub ((rk_d2 he hb ht x y).const_smul (2 : ℝ))
  m0 := fun x => (((whole_meas x).1).add (((whole_meas x).1).comp_measurable
    (measurable_fst.prodMk ((continuous_Rf he).measurable.comp measurable_snd)))).sub
    (stronglyMeasurable_const.mul (sm_rk0 he b x))
  m1 := fun x => (((whole_meas x).2.1).add (((whole_meas x).2.1).comp_measurable
    (measurable_fst.prodMk ((continuous_Rf he).measurable.comp measurable_snd)))).sub
    ((sm_rk1 he b x).const_smul (2 : ℝ))
  m2 := fun x => (((whole_meas x).2.2.1).add (((whole_meas x).2.2.1).comp_measurable
    (measurable_fst.prodMk ((continuous_Rf he).measurable.comp measurable_snd)))).sub
    ((sm_rk2 he b x).const_smul (2 : ℝ))
  m3 := fun x => (((whole_meas x).2.2.2).add (((whole_meas x).2.2.2).comp_measurable
    (measurable_fst.prodMk ((continuous_Rf he).measurable.comp measurable_snd)))).sub
    ((sm_rk3 he b x).const_smul (2 : ℝ))
  b0 := (oK_bounds he hb).1
  b1 := (oK_bounds he hb).2.1
  b2 := (oK_bounds he hb).2.2.1
  b3 := (oK_bounds he hb).2.2.2
  dom := oK_dom he hb
  heat := oK_heat he hb
  mass := oK_mass he hb

lemma obliqueKHyp_plain {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0)
    (K : ℝ → Eu d → Eu d → ℝ) (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ))
    (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)) (A c : ℝ)
    (hK : K = oK e b) (hK1 : K1 = oK1 e b) (hK2 : K2 = oK2 e b) (hK3 : K3 = oK3 e b) (hA : A = oA d b)
    (hc : c = rK b * 4) :
    0 ≤ A ∧ 0 < c ∧ MeasurableSet ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ Convex ℝ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ v w z : EuclideanSpace ℝ (Fin d),
        |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K p.1 x p.2)) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K1 p.1 x p.2)) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K2 p.1 x p.2)) ∧
      (∀ x v w z : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K3 p.1 x p.2 v w z)) ∧
      (∀ t : ℝ, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.IntegrableOn F ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧
          ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasDerivAt (fun t => K t x y)
        ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
      (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), ∫ y in ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), K t x y = 1) := by
  subst hK hK1 hK2 hK3 hA hc
  exact plain_of_khyp (obliqueKHyp he hb)

end Oblique

end ObliqueLib

open ObliqueLib in
set_option maxHeartbeats 1000000 in
theorem solution :
∀ (d : ℕ),
  letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
  letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
  letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
  letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
  letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
  letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
  letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
  letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
  letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
  letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
  letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
  letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
  letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
  letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
  letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
  letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
  let G : (s : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s));
  let Ip : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ);
  let ge : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (rexp (-(a * ‖z‖ ^ 2)));
  let gK1 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((-(2 * a) * ge a z) • Ip z);
  let gK2 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (ge a z • ((4 * a ^ 2) • (Ip z).smulRight (Ip z) - (2 * a) • Ip));
  let gK3 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK2 a) z);
  let hN : (t : ℝ) → ℝ := fun (t : ℝ) => ((π * (2 * t)) ^ (-((d : ℝ) / 2)));
  let wK : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (G (2 * t) (x - y));
  let wK1 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK1 (1 / (2 * t)) (x - y));
  let wK2 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK2 (1 / (2 * t)) (x - y));
  let wK3 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK3 (1 / (2 * t)) (x - y));
  let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
  let Rf : (e x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) := fun (e x : EuclideanSpace ℝ (Fin d)) => (x - (2 * inner ℝ x e) • e);
  let rK : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (14 + 8 * ‖b‖ ^ 2);
  let gK4 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK3 a) z);
  let eb1 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.apply ℝ ℝ b);
  let eb2 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) ℝ (eb1 b));
  let eb3 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (eb2 b));
  let rP0 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t * eb1 b (gK1 (1 / (2 * t)) w));
  let rP1 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb2 b (gK2 (1 / (2 * t)) w));
  let rP2 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb3 b (gK3 (1 / (2 * t)) w));
  let rP3 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • (eb3 b).comp (gK4 (1 / (2 * t)) w));
  let rk0 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP0 b t (x - Rf e y + s • (e - b)));
  let rk1 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP1 b t (x - Rf e y + s • (e - b)));
  let rk2 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP2 b t (x - Rf e y + s • (e - b)));
  let rk3 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP3 b t (x - Rf e y + s • (e - b)));
  let rB : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (rK b ^ ((d : ℝ) / 2) * (√(π * (rK b * 4)) / 2));
  let rA : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (‖b‖ * (2 * wA) * rB b);
  let oK : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK t x y + wK t x (Rf e y) - 2 * rk0 e b t x y);
  let oK1 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK1 t x y + wK1 t x (Rf e y) - (2 : ℝ) • rk1 e b t x y);
  let oK2 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK2 t x y + wK2 t x (Rf e y) - (2 : ℝ) • rk2 e b t x y);
  let oK3 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK3 t x y + wK3 t x (Rf e y) - (2 : ℝ) • rk3 e b t x y);
  let oA : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (2 * wA * rK b ^ ((d : ℝ) / 2) + 2 * rA b);
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (A c : ℝ) (hK : K = oK e b) (hK1 : K1 = oK1 e b) (hK2 : K2 = oK2 e b) (hK3 : K3 = oK3 e b) (hA : A = oA b) (hc : c = rK b * 4), 0 ≤ A ∧ 0 < c ∧ MeasurableSet ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ Convex ℝ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧ (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧ (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧ (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K p.1 x p.2)) ∧ (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K1 p.1 x p.2)) ∧ (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K2 p.1 x p.2)) ∧ (∀ x v w z : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K3 p.1 x p.2 v w z)) ∧ (∀ t : ℝ, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.IntegrableOn F ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧ ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧ (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasDerivAt (fun t => K t x y) ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧ (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), ∫ y in ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), K t x y = 1)) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN wK wK1 wK2 wK3 wA Rf rK gK4 eb1 eb2 eb3 rP0 rP1 rP2 rP3 rk0 rk1 rk2 rk3 rB rA oK oK1 oK2 oK3 oA
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_contDiff_gK2_uncurry, f_continuous_gK1_uncurry, f_continuous_gK3_uncurry, f_sm_hN, f_wK_eq, f_wK2_trace, f_wK_heat, f_whole_meas⟩ := @EthierKurtz.heat_kernel_solves_heat_equation d
  obtain ⟨f_continuous_rP2, f_continuous_rP1, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg, f_rk_d0, f_rk_d1, f_rk_d2, f_rk_bounds_gen, f_rA_nonneg, f_rk_bounds⟩ := @EthierKurtz.ray_kernel_derivative_bounds d
  obtain ⟨f_rk_heat, f_measurableSet_Hs, f_continuous_Rf, f_mp_Rf, f_me_Rf, f_mass_even, f_mass_ray_inner⟩ := @EthierKurtz.ray_kernel_heat_equation_and_mass d
  obtain ⟨f_sm_rk0, f_sm_rk1, f_sm_rk2, f_sm_rk3, f_integrableOn_G_Rf, f_integrableOn_rk0, f_mass_rk0⟩ := @EthierKurtz.ray_kernel_smoothness_and_mass d
  obtain ⟨f_oA_nonneg, f_convex_Hs, f_oK_eq_smul, f_oK_bounds, f_oK_heat, f_oK_mass⟩ := @EthierKurtz.oblique_kernel_bounds_heat_mass d
  have f_oK_dom := @EthierKurtz.oblique_kernel_domination d
  haveI : ObliqueLib.IFacts d := ⟨f_wK_d1, f_wK_d2, f_wK_d3, f_whole_meas, f_rK_pos, f_rk_d0, f_rk_d1, f_rk_d2, f_measurableSet_Hs, f_continuous_Rf, f_sm_rk0, f_sm_rk1, f_sm_rk2, f_sm_rk3, f_oA_nonneg, f_convex_Hs, f_oK_bounds, f_oK_heat, f_oK_mass, f_oK_dom⟩
  exact (fun {e b} he hb K K1 K2 K3 A c hK hK1 hK2 hK3 hA hc => @ObliqueLib.obliqueKHyp_plain d _ e b he hb K K1 K2 K3 A c hK hK1 hK2 hK3 hA hc)
