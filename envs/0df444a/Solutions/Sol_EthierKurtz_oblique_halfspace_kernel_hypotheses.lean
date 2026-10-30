-- Prove2me | solution 1 for EthierKurtz.oblique_halfspace_kernel_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T17:19:09.252634+00:00
-- url     : https://prove2.me/submissions/1b29b79f-c45d-4f2d-83f3-a008732095bd

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_ray_integrand_derivative_bounds
import Theorems.Thm_EthierKurtz_ray_kernel_derivative_bounds
import Theorems.Thm_EthierKurtz_oblique_kernel_satisfies_kernel_hypotheses

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

/-- The constant of the ray integral. -/
noncomputable def rC (d : ℕ) (b : Eu d) (m σ : ℝ) : ℝ :=
  rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * (√(π * (rK b * σ)) / 2)

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

section PlainK

variable {d : ℕ}

end PlainK

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

section Oblique

variable {d : ℕ}

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

end Oblique

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  gK1_apply : ∀ (a : ℝ) (z v : Eu d), gK1 a z v = -(2 * a) * ge d a z * inner ℝ z v
  inner_self_unit : ∀ {e : Eu d} (he : ‖e‖ = 1), inner ℝ e e = (1 : ℝ)
  norm_sub_Rf_sq : ∀ {e : Eu d} (he : ‖e‖ = 1) (x y : Eu d), ‖x - Rf e y‖ ^ 2 = ‖x - y‖ ^ 2 + 4 * inner ℝ x e * inner ℝ y e
  rK_pos : ∀ (b : Eu d), 0 < rK b
  G_ray_le : ∀ {e b z : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m s σ : ℝ} (hm : 0 ≤ m) (hz : -m ≤ inner ℝ z e) (hs : 0 ≤ s) (hσ : 0 < σ), G d σ (z + s • (e - b)) ≤ rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z * rexp (-(1 / (rK b * σ)) * s ^ 2)
  eb1_apply : ∀ (b : Eu d) (M : Eu d →L[ℝ] ℝ), eb1 b M = M b
  rP_d0 : ∀ (b : Eu d) (t : ℝ) (w : Eu d), HasFDerivAt (rP0 b t) (rP1 b t w) w
  rP_bounds : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d), |rP0 b t w| ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) w ∧ ‖rP1 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 : ℝ)) * G d (4 * t) w ∧ ‖rP2 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) w ∧ ‖rP3 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * G d (4 * t) w
  continuous_rP1 : ∀ (b : Eu d) (t : ℝ), Continuous (rP1 b t)
  continuous_rP0 : ∀ (b : Eu d) (t : ℝ), Continuous (rP0 b t)
  rP_b0 : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d), ‖rP0 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) w
  rP_const_nonneg : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (p : ℝ), 0 ≤ ‖b‖ * (2 * wA d) * t ^ p
  obliqueKHyp_plain : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) (K : ℝ → Eu d → Eu d → ℝ) (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)) (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)) (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)) (A c : ℝ) (hK : K = oK e b) (hK1 : K1 = oK1 e b) (hK2 : K2 = oK2 e b) (hK3 : K3 = oK3 e b) (hA : A = oA d b) (hc : c = rK b * 4), 0 ≤ A ∧ 0 < c ∧ MeasurableSet ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ Convex ℝ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧ (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧ (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧ (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧ (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K p.1 x p.2)) ∧ (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K1 p.1 x p.2)) ∧ (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K2 p.1 x p.2)) ∧ (∀ x v w z : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K3 p.1 x p.2 v w z)) ∧ (∀ t : ℝ, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.IntegrableOn F ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧ ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧ (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasDerivAt (fun t => K t x y) ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧ (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), ∫ y in ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), K t x y = 1)

end IFk

export IFacts (gK1_apply inner_self_unit norm_sub_Rf_sq rK_pos G_ray_le eb1_apply rP_d0 rP_bounds continuous_rP1 continuous_rP0 rP_b0 rP_const_nonneg obliqueKHyp_plain)

section HalfGeom_dup

variable {d : ℕ}

variable [IFacts d]

/-- Integral of a Gaussian-dominated function along the ray `z + s (e - b)`, `s > 0`. -/
lemma ray_integral_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e b z : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m σ M : ℝ} (hm : 0 ≤ m)
    (hz : -m ≤ inner ℝ z e) (hσ : 0 < σ) (hM : 0 ≤ M) {φ : Eu d → F} (hφc : Continuous φ)
    (hφ : ∀ w, ‖φ w‖ ≤ M * G d σ w) :
    IntegrableOn (fun s : ℝ => φ (z + s • (e - b))) (Ioi (0 : ℝ)) ∧
      ‖∫ s in Ioi (0 : ℝ), φ (z + s • (e - b))‖ ≤ M * rC d b m σ * G d (rK b * σ) z := by
  have hK := rK_pos b
  have hKσ : 0 < rK b * σ := mul_pos hK hσ
  set C0 := M * (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z) with hC0
  have hgi : Integrable (fun s : ℝ => C0 * rexp (-(1 / (rK b * σ)) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul C0
  have hcont : Continuous (fun s : ℝ => φ (z + s • (e - b))) :=
    hφc.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hpt : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖φ (z + s • (e - b))‖ ≤ C0 * rexp (-(1 / (rK b * σ)) * s ^ 2) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    have h1 := G_ray_le (d := d) he hb hm hz (le_of_lt hs) hσ
    calc ‖φ (z + s • (e - b))‖ ≤ M * G d σ (z + s • (e - b)) := hφ _
      _ ≤ M * (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z *
            rexp (-(1 / (rK b * σ)) * s ^ 2)) := mul_le_mul_of_nonneg_left h1 hM
      _ = C0 * rexp (-(1 / (rK b * σ)) * s ^ 2) := by rw [hC0]; ring
  refine ⟨hgi.integrableOn.mono' hcont.aestronglyMeasurable hpt, ?_⟩
  calc ‖∫ s in Ioi (0 : ℝ), φ (z + s • (e - b))‖
      ≤ ∫ s in Ioi (0 : ℝ), C0 * rexp (-(1 / (rK b * σ)) * s ^ 2) :=
        norm_integral_le_of_norm_le hgi.integrableOn hpt
    _ = C0 * (√(π / (1 / (rK b * σ))) / 2) := by rw [integral_const_mul, integral_gaussian_Ioi]
    _ = M * rC d b m σ * G d (rK b * σ) z := by
        rw [hC0, rC, show π / (1 / (rK b * σ)) = π * (rK b * σ) by field_simp]; ring

end HalfGeom_dup

section OblBC

variable {d : ℕ}

variable [IFacts d]

noncomputable local instance instL2N13 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S13 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N13 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S13 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma rk1_apply_bc {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t)
    (x y : Eu d) : rk1 e b t x y (b - e) = rP0 b t (x - Rf e y) := by
  set z := x - Rf e y
  set v := e - b
  have hK := rK_pos b
  have hm := neg_abs_le (inner ℝ z e)
  have hI1 := (ray_integral_bound he hb (abs_nonneg _) hm (by positivity : 0 < 4 * t)
    (rP_const_nonneg b ht _) (continuous_rP1 b t) (fun w => (rP_bounds b ht w).2.1)).1
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => rP0 b t (z + s • v)) (rP1 b t (z + s • v) v) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => z + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add z
    exact (rP_d0 b t (z + s • v)).comp_hasDerivAt s hl
  have hcont : Continuous (fun s : ℝ => rP0 b t (z + s • v)) :=
    (continuous_rP0 b t).comp (continuous_const.add (continuous_id.smul continuous_const))
  have htend : Tendsto (fun s : ℝ => rP0 b t (z + s • v)) atTop (𝓝 0) := by
    set M := ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ))
    set K := M * (rK b ^ ((d : ℝ) / 2) * rexp (|inner ℝ z e| ^ 2 / (4 * t)) *
      G d (rK b * (4 * t)) z)
    set c := 1 / (rK b * (4 * t))
    have hc : 0 < c := by positivity
    have hlim : Tendsto (fun s : ℝ => K * rexp (-c * s ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => -c * s ^ 2) atTop atBot :=
        (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith)
      have := (Real.tendsto_exp_atBot.comp h1).const_mul K
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    calc ‖rP0 b t (z + s • v)‖ ≤ M * G d (4 * t) (z + s • v) := rP_b0 b ht _
      _ ≤ M * (rK b ^ ((d : ℝ) / 2) * rexp (|inner ℝ z e| ^ 2 / (4 * t)) * G d (rK b * (4 * t)) z *
            rexp (-c * s ^ 2)) :=
          mul_le_mul_of_nonneg_left (G_ray_le he hb (abs_nonneg _) hm hs (by positivity))
            (rP_const_nonneg b ht _)
      _ = K * rexp (-c * s ^ 2) := by ring
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
    (fun s _ => hderiv s) (hI1.apply_continuousLinearMap v) htend
  show (∫ s in Ioi (0 : ℝ), rP1 b t (z + s • v)) (b - e) = rP0 b t z
  rw [ContinuousLinearMap.integral_apply hI1, show b - e = -v from (neg_sub e b).symm]
  simp only [map_neg, integral_neg]
  show -∫ s in Ioi (0 : ℝ), rP1 b t (z + s • v) v = rP0 b t z
  rw [hF, zero_smul, add_zero, zero_sub, neg_neg]

/-- Kernel-level oblique boundary condition: `D_x oK · (b - e) = 0` when `⟪x, e⟫ = 0`. -/
lemma oK1_bc {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t)
    {x : Eu d} (hx : inner ℝ x e = 0) (y : Eu d) : oK1 e b t x y (b - e) = 0 := by
  have h1 := rk1_apply_bc he hb ht x y
  simp only [oK1, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, h1]
  simp only [wK1, rP0, eb1_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, gK1_apply]
  have hge : ge d (1 / (2 * t)) (x - Rf e y) = ge d (1 / (2 * t)) (x - y) := by
    unfold ge; rw [norm_sub_Rf_sq he, hx]; simp only [mul_zero, zero_mul, add_zero]
  have hR : x - Rf e y = (x - y) + (2 * inner ℝ y e) • e := by simp only [Rf]; abel
  have heb : inner ℝ e b = (0 : ℝ) := by rw [real_inner_comm]; exact hb
  have hee := inner_self_unit he
  have i1 : inner ℝ (x - y) (b - e) = inner ℝ x b - inner ℝ y b + inner ℝ y e := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hx]; ring
  have i2 : inner ℝ (x - Rf e y) (b - e) = inner ℝ x b - inner ℝ y b - inner ℝ y e := by
    rw [hR, inner_add_left, real_inner_smul_left, i1, inner_sub_right, heb, hee]; ring
  have i3 : inner ℝ (x - Rf e y) b = inner ℝ x b - inner ℝ y b := by
    rw [hR, inner_add_left, real_inner_smul_left, inner_sub_left, heb]; ring
  rw [hge, i1, i2, i3]; ring

end OblBC

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
    ∀ (e b : EuclideanSpace ℝ (Fin d)), ‖e‖ = 1 → inner ℝ b e = 0 →
    ∃ (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
      (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
      (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
      (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
      (A c : ℝ),
    (0 ≤ A ∧ 0 < c ∧ MeasurableSet ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ Convex ℝ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧
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
      (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), ∫ y in ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), K t x y = 1)) ∧
    (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → ∀ y : EuclideanSpace ℝ (Fin d), K1 t x y (b - e) = 0) := by
  intro d
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_eb1_apply, f_rP_d0, f_rP_d1, f_rP_d2, f_rP_bounds⟩ := @EthierKurtz.ray_integrand_derivative_bounds d
  obtain ⟨f_continuous_rP2, f_continuous_rP1, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg, f_rk_d0, f_rk_d1, f_rk_d2, f_rk_bounds_gen, f_rA_nonneg, f_rk_bounds⟩ := @EthierKurtz.ray_kernel_derivative_bounds d
  have f_obliqueKHyp_plain := @EthierKurtz.oblique_kernel_satisfies_kernel_hypotheses d
  haveI : ObliqueLib.IFacts d := ⟨f_gK1_apply, f_inner_self_unit, f_norm_sub_Rf_sq, f_rK_pos, f_G_ray_le, f_eb1_apply, f_rP_d0, f_rP_bounds, f_continuous_rP1, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg, f_obliqueKHyp_plain⟩
  intro e b he hb
  exact ⟨ObliqueLib.oK e b, ObliqueLib.oK1 e b, ObliqueLib.oK2 e b, ObliqueLib.oK3 e b, ObliqueLib.oA d b, ObliqueLib.rK b * 4,
    ObliqueLib.obliqueKHyp_plain he hb _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl, fun t ht x hx y => ObliqueLib.oK1_bc he hb ht hx y⟩
