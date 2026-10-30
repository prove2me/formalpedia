-- Prove2me | solution 1 for EthierKurtz.oblique_kernel_bounds_heat_mass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T16:26:33.153612+00:00
-- url     : https://prove2.me/submissions/c48f87ec-2741-4b66-b6c8-a2ba98ff7773

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_heat_kernel_solves_heat_equation
import Theorems.Thm_EthierKurtz_ray_kernel_derivative_bounds
import Theorems.Thm_EthierKurtz_ray_kernel_heat_equation_and_mass
import Theorems.Thm_EthierKurtz_ray_kernel_smoothness_and_mass

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

lemma integrable_exp_sq {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Eu d => rexp (-b * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Eu d)
    (b := (b : ℂ)) (by simpa using hb) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun v => ?_)
  have : (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * ((inner ℝ (0 : Eu d) v : ℝ) : ℂ))
      = ((-b * ‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  simp only [this, Complex.norm_exp_ofReal]

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

lemma G_eq {d : ℕ} {s : ℝ} (z : Eu d) :
    G d s z = (π * s) ^ (-((d : ℝ) / 2)) * rexp (-(1 / s) * ‖z‖ ^ 2) := by
  rw [G]; congr 2; ring

lemma integrable_G {d : ℕ} {s : ℝ} (hs : 0 < s) : Integrable (G d s) := by
  have h := (integrable_exp_sq (d := d) (b := 1 / s) (by positivity)).const_mul
    ((π * s) ^ (-((d : ℝ) / 2)))
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  rw [G_eq]

lemma integrable_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Eu d) :
    Integrable (fun y : Eu d => G d s (x - y)) :=
  (integrable_G hs).comp_sub_left x

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

/-- Trace of a bilinear form in the standard basis (twice the generator `Δ/2` acts as `lap2/2`). -/
noncomputable def lap2 {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

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

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  wA_nonneg : 0 ≤ wA d
  whole_bounds : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), |wK d t x y| ≤ wA d * G d (4 * t) (x - y) ∧ ‖wK1 t x y‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK2 t x y‖ ≤ wA d * t ^ (-(1 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK3 t x y‖ ≤ wA d * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) (x - y)
  wK_heat : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), HasDerivAt (fun t => wK d t x y) ((1 / 2 : ℝ) * lap2 (wK2 t x y)) t
  G_Rf_le : ∀ {e : Eu d} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) {x y : Eu d} (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e), G d s (x - Rf e y) ≤ G d s (x - y)
  G_mono_s : ∀ {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') (z : Eu d), G d s z ≤ (s' / s) ^ ((d : ℝ) / 2) * G d s' z
  one_le_rK : ∀ (b : Eu d), 1 ≤ rK b
  rK_pos : ∀ (b : Eu d), 0 < rK b
  rC_nonneg : ∀ (b : Eu d) (m σ : ℝ), 0 ≤ rC d b m σ
  rA_nonneg : ∀ (b : Eu d), 0 ≤ rA d b
  rk_bounds : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) {x y : Eu d} (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e), |rk0 e b t x y| ≤ rA d b * G d (rK b * (4 * t)) (x - y) ∧ ‖rk1 e b t x y‖ ≤ rA d b * t ^ (-(1 / 2 : ℝ)) * G d (rK b * (4 * t)) (x - y) ∧ ‖rk2 e b t x y‖ ≤ rA d b * t ^ (-(1 : ℝ)) * G d (rK b * (4 * t)) (x - y) ∧ ‖rk3 e b t x y‖ ≤ rA d b * t ^ (-(3 / 2 : ℝ)) * G d (rK b * (4 * t)) (x - y)
  rk_heat : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : Eu d), HasDerivAt (fun t => rk0 e b t x y) ((1 / 2 : ℝ) * lap2 (rk2 e b t x y)) t
  mass_even : ∀ {e : Eu d} (he : ‖e‖ = 1) {t : ℝ} (ht : 0 < t) (x : Eu d), (∫ y in Hs e, wK d t x y) + ∫ y in Hs e, wK d t x (Rf e y) = 1
  integrableOn_G_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) (x : Eu d) (S : Set (Eu d)), IntegrableOn (fun y => G d s (x - Rf e y)) S
  integrableOn_rk0 : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x : Eu d), IntegrableOn (fun y => rk0 e b t x y) (Hs e)
  mass_rk0 : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x : Eu d), ∫ y in Hs e, rk0 e b t x y = 0

end IFk

export IFacts (wA_nonneg whole_bounds wK_heat G_Rf_le G_mono_s one_le_rK rK_pos rC_nonneg rA_nonneg rk_bounds rk_heat mass_even integrableOn_G_Rf integrableOn_rk0 mass_rk0)

section OblDomA

variable {d : ℕ}

variable [IFacts d]

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

lemma oA_nonneg (b : Eu d) : 0 ≤ oA d b := by
  have := wA_nonneg (d := d); have := rA_nonneg (d := d) b; have := rK_pos b
  unfold oA; positivity

lemma G4_le (b : Eu d) {t : ℝ} (ht : 0 < t) (z : Eu d) :
    G d (4 * t) z ≤ rK b ^ ((d : ℝ) / 2) * G d (rK b * (4 * t)) z := by
  have h1 := one_le_rK b
  have := G_mono_s (d := d) (by positivity : 0 < 4 * t) (s' := rK b * (4 * t)) (by nlinarith) z
  rwa [show rK b * (4 * t) / (4 * t) = rK b by field_simp] at this

lemma norm_comb_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A B C : F) :
    ‖A + B - (2 : ℝ) • C‖ ≤ ‖A‖ + ‖B‖ + 2 * ‖C‖ := by
  calc ‖A + B - (2 : ℝ) • C‖ ≤ ‖A + B‖ + ‖(2 : ℝ) • C‖ := norm_sub_le _ _
    _ ≤ ‖A‖ + ‖B‖ + 2 * ‖C‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [norm_add_le A B]

/-- Gaussian bound of a kernel combination on the half-space. -/
lemma comb_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e b : Eu d}
    (he : ‖e‖ = 1) {t p : ℝ} (ht : 0 < t) (hp : 0 ≤ p) {x y : Eu d} (hx : x ∈ Hs e)
    (hy : y ∈ Hs e) {A B C : F} (hA : ‖A‖ ≤ wA d * p * G d (4 * t) (x - y))
    (hB : ‖B‖ ≤ wA d * p * G d (4 * t) (x - Rf e y))
    (hC : ‖C‖ ≤ rA d b * p * G d (rK b * (4 * t)) (x - y)) :
    ‖A + B - (2 : ℝ) • C‖ ≤ oA d b * p * G d (rK b * 4 * t) (x - y) := by
  have h1 := G_Rf_le (d := d) he (by positivity : 0 < 4 * t) hx hy
  have h2 := G4_le b ht (x - y)
  have hW := wA_nonneg (d := d)
  have a2 : ‖B‖ ≤ wA d * p * G d (4 * t) (x - y) :=
    hB.trans (mul_le_mul_of_nonneg_left h1 (mul_nonneg hW hp))
  have a3 : wA d * p * G d (4 * t) (x - y) ≤
      wA d * p * (rK b ^ ((d : ℝ) / 2) * G d (rK b * (4 * t)) (x - y)) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hW hp)
  rw [show rK b * 4 * t = rK b * (4 * t) by ring]
  refine (norm_comb_le A B C).trans ?_
  unfold oA
  linarith

lemma lap2_comb (A B C : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :
    lap2 (A + B - (2 : ℝ) • C) = lap2 A + lap2 B - 2 * lap2 C := by
  unfold lap2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

lemma convex_Hs (e : Eu d) : Convex ℝ (Hs e) := by
  intro x hx y hy a c ha hc _
  show 0 ≤ inner ℝ (a • x + c • y) e
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hc hy)

lemma oK_eq_smul (e b : Eu d) (t : ℝ) (x y : Eu d) :
    oK e b t x y = wK d t x y + wK d t x (Rf e y) - (2 : ℝ) • rk0 e b t x y := by
  rw [smul_eq_mul]; rfl

/-- The oblique half-space heat kernel satisfies the kernel hypotheses on `Hs e`. -/
lemma oK_bounds {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) :
    (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, |oK e b t x y| ≤ oA d b * G d (rK b * 4 * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK1 e b t x y‖ ≤ oA d b * t ^ (-(1 / 2 : ℝ)) * G d (rK b * 4 * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK2 e b t x y‖ ≤ oA d b * t ^ (-(1 : ℝ)) * G d (rK b * 4 * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK3 e b t x y‖ ≤ oA d b * t ^ (-(3 / 2 : ℝ)) * G d (rK b * 4 * t) (x - y)) := by
  refine ⟨fun t ht x hx y hy => ?_, fun t ht x hx y hy => ?_, fun t ht x hx y hy => ?_, fun t ht x hx y hy => ?_⟩
  · obtain ⟨w0, -, -, -⟩ := whole_bounds (d := d) ht x y
    obtain ⟨v0, -, -, -⟩ := whole_bounds (d := d) ht x (Rf e y)
    have r0 := (rk_bounds he hb ht hx hy).1
    have := comb_bound (F := ℝ) he ht zero_le_one hx hy (A := wK d t x y) (B := wK d t x (Rf e y))
      (C := rk0 e b t x y) (by rw [Real.norm_eq_abs, mul_one]; exact w0)
      (by rw [Real.norm_eq_abs, mul_one]; exact v0) (by rw [Real.norm_eq_abs, mul_one]; exact r0)
    rw [oK_eq_smul, ← Real.norm_eq_abs]
    rwa [mul_one] at this
  · exact comb_bound he ht (rpow_nonneg ht.le _) hx hy
      (whole_bounds (d := d) ht x y).2.1 (whole_bounds (d := d) ht x (Rf e y)).2.1
      (rk_bounds he hb ht hx hy).2.1
  · exact comb_bound he ht (rpow_nonneg ht.le _) hx hy
      (whole_bounds (d := d) ht x y).2.2.1 (whole_bounds (d := d) ht x (Rf e y)).2.2.1
      (rk_bounds he hb ht hx hy).2.2.1
  · exact comb_bound he ht (rpow_nonneg ht.le _) hx hy
      (whole_bounds (d := d) ht x y).2.2.2 (whole_bounds (d := d) ht x (Rf e y)).2.2.2
      (rk_bounds he hb ht hx hy).2.2.2

lemma oK_heat {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) :
    ∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => oK e b t x y)
      ((1 / 2 : ℝ) * ∑ i, oK2 e b t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t := by
  intro t ht x y
  have h := ((wK_heat ht x y).add (wK_heat ht x (Rf e y))).sub ((rk_heat he hb ht x y).const_mul 2)
  refine h.congr_deriv ?_
  show _ = (1 / 2 : ℝ) * lap2 (oK2 e b t x y)
  rw [oK2, lap2_comb]; ring

lemma oK_mass {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) :
    ∀ t, 0 < t → ∀ x, ∫ y in Hs e, oK e b t x y = 1 := by
  intro t ht x
  have i1 : IntegrableOn (fun y => wK d t x y) (Hs e) :=
    (integrable_G_sub (s := 2 * t) (by positivity) x).integrableOn
  have i2 : IntegrableOn (fun y => wK d t x (Rf e y)) (Hs e) :=
    integrableOn_G_Rf he (s := 2 * t) (by positivity) x (Hs e)
  have i3 := integrableOn_rk0 he hb ht x
  show ∫ y in Hs e, (wK d t x y + wK d t x (Rf e y) - 2 * rk0 e b t x y) = 1
  rw [show (∫ y in Hs e, (wK d t x y + wK d t x (Rf e y) - 2 * rk0 e b t x y))
      = (∫ y in Hs e, (wK d t x y + wK d t x (Rf e y))) - ∫ y in Hs e, 2 * rk0 e b t x y
      from integral_sub (i1.add i2) (i3.const_mul 2)]
  rw [show (∫ y in Hs e, (wK d t x y + wK d t x (Rf e y)))
      = (∫ y in Hs e, wK d t x y) + ∫ y in Hs e, wK d t x (Rf e y) from integral_add i1 i2]
  rw [integral_const_mul, mass_rk0 he hb ht x, mass_even he ht x]
  ring

end OblDomA

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
  let Hs : (e : EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d)) := fun (e : EuclideanSpace ℝ (Fin d)) => ({y | 0 ≤ inner ℝ y e});
  let oK : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK t x y + wK t x (Rf e y) - 2 * rk0 e b t x y);
  let oK1 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK1 t x y + wK1 t x (Rf e y) - (2 : ℝ) • rk1 e b t x y);
  let oK2 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK2 t x y + wK2 t x (Rf e y) - (2 : ℝ) • rk2 e b t x y);
  let oK3 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK3 t x y + wK3 t x (Rf e y) - (2 : ℝ) • rk3 e b t x y);
  let oA : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (2 * wA * rK b ^ ((d : ℝ) / 2) + 2 * rA b);
    (∀ (b : EuclideanSpace ℝ (Fin d)), 0 ≤ oA b) ∧
    (∀ (e : EuclideanSpace ℝ (Fin d)), Convex ℝ (Hs e)) ∧
    (∀ (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)), oK e b t x y = wK t x y + wK t x (Rf e y) - (2 : ℝ) • rk0 e b t x y) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0), (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, |oK e b t x y| ≤ oA b * G (rK b * 4 * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK1 e b t x y‖ ≤ oA b * t ^ (-(1 / 2 : ℝ)) * G (rK b * 4 * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK2 e b t x y‖ ≤ oA b * t ^ (-(1 : ℝ)) * G (rK b * 4 * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ Hs e, ∀ y ∈ Hs e, ‖oK3 e b t x y‖ ≤ oA b * t ^ (-(3 / 2 : ℝ)) * G (rK b * 4 * t) (x - y))) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0), ∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => oK e b t x y) ((1 / 2 : ℝ) * ∑ i, oK2 e b t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0), ∀ t, 0 < t → ∀ x, ∫ y in Hs e, oK e b t x y = 1) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN wK wK1 wK2 wK3 wA Rf rK gK4 eb1 eb2 eb3 rP0 rP1 rP2 rP3 rk0 rk1 rk2 rk3 rB rA Hs oK oK1 oK2 oK3 oA
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_contDiff_gK2_uncurry, f_continuous_gK1_uncurry, f_continuous_gK3_uncurry, f_sm_hN, f_wK_eq, f_wK2_trace, f_wK_heat, f_whole_meas⟩ := @EthierKurtz.heat_kernel_solves_heat_equation d
  obtain ⟨f_continuous_rP2, f_continuous_rP1, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg, f_rk_d0, f_rk_d1, f_rk_d2, f_rk_bounds_gen, f_rA_nonneg, f_rk_bounds⟩ := @EthierKurtz.ray_kernel_derivative_bounds d
  obtain ⟨f_rk_heat, f_measurableSet_Hs, f_continuous_Rf, f_mp_Rf, f_me_Rf, f_mass_even, f_mass_ray_inner⟩ := @EthierKurtz.ray_kernel_heat_equation_and_mass d
  obtain ⟨f_sm_rk0, f_sm_rk1, f_sm_rk2, f_sm_rk3, f_integrableOn_G_Rf, f_integrableOn_rk0, f_mass_rk0⟩ := @EthierKurtz.ray_kernel_smoothness_and_mass d
  haveI : ObliqueLib.IFacts d := ⟨f_wA_nonneg, f_whole_bounds, f_wK_heat, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_rC_nonneg, f_rA_nonneg, f_rk_bounds, f_rk_heat, f_mass_even, f_integrableOn_G_Rf, f_integrableOn_rk0, f_mass_rk0⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fun b => @ObliqueLib.oA_nonneg d _ b)
  · exact (fun e => @ObliqueLib.convex_Hs d _ e)
  · exact (fun e b t x y => @ObliqueLib.oK_eq_smul d _ e b t x y)
  · exact (fun {e b} he hb => @ObliqueLib.oK_bounds d _ e b he hb)
  · exact (fun {e b} he hb => @ObliqueLib.oK_heat d _ e b he hb)
  · exact (fun {e b} he hb => @ObliqueLib.oK_mass d _ e b he hb)
