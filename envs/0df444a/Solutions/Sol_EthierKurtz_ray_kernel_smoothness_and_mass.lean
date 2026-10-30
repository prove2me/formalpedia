-- Prove2me | solution 1 for EthierKurtz.ray_kernel_smoothness_and_mass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T15:05:43.444278+00:00
-- url     : https://prove2.me/submissions/8c4afbbd-82a2-4b1c-8baf-64b114e9522c

import Mathlib
import Theorems.Thm_EthierKurtz_heat_kernel_solves_heat_equation
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_ray_kernel_derivative_bounds
import Theorems.Thm_EthierKurtz_ray_kernel_heat_equation_and_mass

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

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  contDiff_gK2_uncurry : ContDiff ℝ ⊤ (fun p : ℝ × Eu d => gK2 p.1 p.2)
  continuous_gK1_uncurry : Continuous (fun p : ℝ × Eu d => gK1 p.1 p.2)
  continuous_gK3_uncurry : Continuous (fun p : ℝ × Eu d => gK3 p.1 p.2)
  sm_hN : StronglyMeasurable (fun p : ℝ × Eu d => hN d p.1)
  inner_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1) (x : Eu d), inner ℝ (Rf e x) e = -inner ℝ x e
  rK_pos : ∀ (b : Eu d), 0 < rK b
  G_ray_le : ∀ {e b z : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m s σ : ℝ} (hm : 0 ≤ m) (hz : -m ≤ inner ℝ z e) (hs : 0 ≤ s) (hσ : 0 < σ), G d σ (z + s • (e - b)) ≤ rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z * rexp (-(1 / (rK b * σ)) * s ^ 2)
  continuous_rP0 : ∀ (b : Eu d) (t : ℝ), Continuous (rP0 b t)
  rP_b0 : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d), ‖rP0 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) w
  rP_const_nonneg : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (p : ℝ), 0 ≤ ‖b‖ * (2 * wA d) * t ^ p
  rk_bounds_gen : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t m : ℝ} (ht : 0 < t) (hm : 0 ≤ m) {x y : Eu d} (hxy : -m ≤ inner ℝ (x - Rf e y) e), |rk0 e b t x y| ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk1 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 : ℝ)) * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk2 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(3 / 2 : ℝ)) * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk3 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y)
  measurableSet_Hs : ∀ (e : Eu d), MeasurableSet (Hs e)
  continuous_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1), Continuous (Rf e)
  mp_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1), MeasurePreserving (Rf e) volume volume
  me_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1), MeasurableEmbedding (Rf e)
  mass_ray_inner : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (w : Eu d), ∫ y in Hs e, rP0 b t (w - Rf e y) = 0

end IFk

export IFacts (contDiff_gK2_uncurry continuous_gK1_uncurry continuous_gK3_uncurry sm_hN inner_Rf rK_pos G_ray_le continuous_rP0 rP_b0 rP_const_nonneg rk_bounds_gen measurableSet_Hs continuous_Rf mp_Rf me_Rf mass_ray_inner)

section Mass_dup

variable {d : ℕ}

noncomputable local instance instL2N10_dup (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S10_dup (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable [IFacts d]

lemma integrable_comp_Rf {E' : Type*} [NormedAddCommGroup E'] {e : Eu d} (he : ‖e‖ = 1)
    {f : Eu d → E'} (hf : Integrable f) : Integrable (fun y => f (Rf e y)) :=
  ((mp_Rf he).integrable_comp_emb (me_Rf he)).mpr hf

end Mass_dup

section RayMeas

variable {d : ℕ}

variable [IFacts d]

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

lemma contDiff_gK3_uncurry : ContDiff ℝ ⊤ (fun p : ℝ × Eu d => gK3 p.1 p.2) :=
  ContDiff.fderiv (𝕜 := ℝ) (m := ⊤) (n := ⊤)
    (f := fun (q : ℝ × Eu d) (z : Eu d) => gK2 q.1 z) (g := fun q => q.2)
    (contDiff_gK2_uncurry.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd le_top

lemma continuous_gK4_uncurry : Continuous (fun p : ℝ × Eu d => gK4 p.1 p.2) :=
  (ContDiff.fderiv (𝕜 := ℝ) (m := ⊤) (n := 0)
    (f := fun (q : ℝ × Eu d) (z : Eu d) => gK3 q.1 z) (g := fun q => q.2)
    (contDiff_gK3_uncurry.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd le_top).continuous

/-- The measurable parameter map `((t, y), s) ↦ (1/(2t), x - Rf e y + s (e - b))`. -/
lemma meas_ray_arg {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d) :
    Measurable (fun q : (ℝ × Eu d) × ℝ =>
      ((1 / (2 * q.1.1) : ℝ), x - Rf e q.1.2 + q.2 • (e - b))) :=
  (measurable_const.div (measurable_const.mul measurable_fst.fst)).prodMk
    ((measurable_const.sub ((continuous_Rf he).measurable.comp measurable_fst.snd)).add
      (measurable_snd.smul measurable_const))

lemma sm_hN_fst : StronglyMeasurable (fun q : (ℝ × Eu d) × ℝ => hN d q.1.1) :=
  (sm_hN (d := d)).comp_measurable measurable_fst

lemma sm_rk0 {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d) :
    StronglyMeasurable (fun p : ℝ × Eu d => rk0 e b p.1 x p.2) := by
  have hc : Continuous (fun p : ℝ × Eu d => eb1 b (gK1 p.1 p.2)) :=
    (eb1 b).continuous.comp continuous_gK1_uncurry
  exact (sm_hN_fst.mul (hc.comp_stronglyMeasurable (meas_ray_arg he b x).stronglyMeasurable)
    ).integral_prod_right'

lemma sm_rk1 {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d) :
    StronglyMeasurable (fun p : ℝ × Eu d => rk1 e b p.1 x p.2) := by
  have hc : Continuous (fun p : ℝ × Eu d => eb2 b (gK2 p.1 p.2)) :=
    (eb2 b).continuous.comp contDiff_gK2_uncurry.continuous
  exact (sm_hN_fst.smul (hc.comp_stronglyMeasurable (meas_ray_arg he b x).stronglyMeasurable)
    ).integral_prod_right'

lemma sm_rk2 {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d) :
    StronglyMeasurable (fun p : ℝ × Eu d => rk2 e b p.1 x p.2) := by
  have hc : Continuous (fun p : ℝ × Eu d => eb3 b (gK3 p.1 p.2)) :=
    (eb3 b).continuous.comp continuous_gK3_uncurry
  exact (sm_hN_fst.smul (hc.comp_stronglyMeasurable (meas_ray_arg he b x).stronglyMeasurable)
    ).integral_prod_right'

lemma sm_rk3 {e : Eu d} (he : ‖e‖ = 1) (b x : Eu d) :
    StronglyMeasurable (fun p : ℝ × Eu d => rk3 e b p.1 x p.2) := by
  have hc : Continuous (fun p : ℝ × Eu d => (eb3 b).comp (gK4 p.1 p.2)) :=
    continuous_const.clm_comp continuous_gK4_uncurry
  exact (sm_hN_fst.smul (hc.comp_stronglyMeasurable (meas_ray_arg he b x).stronglyMeasurable)
    ).integral_prod_right'

lemma inner_sub_Rf_ge {e : Eu d} (he : ‖e‖ = 1) {x y : Eu d} (hy : y ∈ Hs e) :
    -|inner ℝ x e| ≤ inner ℝ (x - Rf e y) e := by
  have : 0 ≤ inner ℝ y e := hy
  rw [inner_sub_left, inner_Rf he]
  linarith [neg_abs_le (inner ℝ x e)]

lemma integrableOn_G_Rf {e : Eu d} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) (x : Eu d) (S : Set (Eu d)) :
    IntegrableOn (fun y => G d s (x - Rf e y)) S :=
  (integrable_comp_Rf he (f := fun y => G d s (x - y)) (integrable_G_sub hs x)).integrableOn

/-- `rk0` is integrable in `y` over the half-space. -/
lemma integrableOn_rk0 {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t)
    (x : Eu d) : IntegrableOn (fun y => rk0 e b t x y) (Hs e) := by
  have hK := rK_pos b
  have hm := (sm_rk0 he b x).comp_measurable (measurable_const.prodMk measurable_id :
    Measurable (fun y : Eu d => (t, y)))
  refine Integrable.mono' ((integrableOn_G_Rf he (by positivity : 0 < rK b * (4 * t)) x (Hs e)).const_mul
    (‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * rC d b |inner ℝ x e| (4 * t)))
    hm.aestronglyMeasurable ((ae_restrict_iff' (measurableSet_Hs e)).mpr
      (Eventually.of_forall fun y hy => ?_))
  rw [Real.norm_eq_abs]
  exact (rk_bounds_gen he hb ht (abs_nonneg _) (inner_sub_Rf_ge he hy)).1

/-- The ray kernel has zero mass on the half-space. -/
lemma mass_rk0 {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t)
    (x : Eu d) : ∫ y in Hs e, rk0 e b t x y = 0 := by
  have hK := rK_pos b
  set v := e - b
  set m := |inner ℝ x e|
  set M := ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ))
  have hM : 0 ≤ M := rP_const_nonneg b ht _
  set K0 := M * (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / (4 * t)))
  have hint : Integrable (Function.uncurry fun (y : Eu d) (s : ℝ) => rP0 b t (x - Rf e y + s • v))
      ((volume.restrict (Hs e)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hg : Integrable (fun q : Eu d × ℝ => K0 * (G d (rK b * (4 * t)) (x - Rf e q.1) *
        rexp (-(1 / (rK b * (4 * t))) * q.2 ^ 2)))
        ((volume.restrict (Hs e)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      (Integrable.mul_prod (integrableOn_G_Rf he (by positivity) x (Hs e))
        (integrable_exp_neg_mul_sq (by positivity)).integrableOn).const_mul K0
    refine hg.mono' ?_ ?_
    · exact ((continuous_rP0 b t).comp ((continuous_const.sub ((continuous_Rf he).comp
        continuous_fst)).add (continuous_snd.smul continuous_const))).aestronglyMeasurable
    · rw [Measure.prod_restrict, ae_restrict_iff' ((measurableSet_Hs e).prod measurableSet_Ioi)]
      refine Eventually.of_forall fun q hq => ?_
      obtain ⟨hy, hs⟩ := hq
      have h1 := G_ray_le (d := d) he hb (abs_nonneg _) (inner_sub_Rf_ge (x := x) he hy) (le_of_lt hs)
        (by positivity : 0 < 4 * t)
      calc ‖rP0 b t (x - Rf e q.1 + q.2 • v)‖ ≤ M * G d (4 * t) (x - Rf e q.1 + q.2 • v) :=
            rP_b0 b ht _
        _ ≤ M * (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / (4 * t)) * G d (rK b * (4 * t)) (x - Rf e q.1) *
              rexp (-(1 / (rK b * (4 * t))) * q.2 ^ 2)) := mul_le_mul_of_nonneg_left h1 hM
        _ = _ := by ring
  unfold rk0
  rw [show (∫ y in Hs e, ∫ s in Ioi (0 : ℝ), rP0 b t (x - Rf e y + s • v))
      = ∫ s in Ioi (0 : ℝ), ∫ y in Hs e, rP0 b t (x - Rf e y + s • v) from
    integral_integral_swap hint]
  refine (integral_congr_ae (Eventually.of_forall fun s => ?_)).trans (integral_zero _ _)
  show ∫ y in Hs e, rP0 b t (x - Rf e y + s • v) = 0
  have : ∀ y, x - Rf e y + s • v = (x + s • v) - Rf e y := fun y => by abel
  simp only [this]
  exact mass_ray_inner he hb ht (x + s • v)

end RayMeas

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
  let Rf : (e x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) := fun (e x : EuclideanSpace ℝ (Fin d)) => (x - (2 * inner ℝ x e) • e);
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
  let Hs : (e : EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d)) := fun (e : EuclideanSpace ℝ (Fin d)) => ({y | 0 ≤ inner ℝ y e});
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (b x : EuclideanSpace ℝ (Fin d)), StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => rk0 e b p.1 x p.2)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (b x : EuclideanSpace ℝ (Fin d)), StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => rk1 e b p.1 x p.2)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (b x : EuclideanSpace ℝ (Fin d)), StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => rk2 e b p.1 x p.2)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (b x : EuclideanSpace ℝ (Fin d)), StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => rk3 e b p.1 x p.2)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin d)) (S : Set (EuclideanSpace ℝ (Fin d))), IntegrableOn (fun y => G s (x - Rf e y)) S) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), IntegrableOn (fun y => rk0 e b t x y) (Hs e)) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), ∫ y in Hs e, rk0 e b t x y = 0) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN Rf gK4 eb1 eb2 eb3 rP0 rP1 rP2 rP3 rk0 rk1 rk2 rk3 Hs
  obtain ⟨f_contDiff_gK2_uncurry, f_continuous_gK1_uncurry, f_continuous_gK3_uncurry, f_sm_hN, f_wK_eq, f_wK2_trace, f_wK_heat, f_whole_meas⟩ := @EthierKurtz.heat_kernel_solves_heat_equation d
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_continuous_rP2, f_continuous_rP1, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg, f_rk_d0, f_rk_d1, f_rk_d2, f_rk_bounds_gen, f_rA_nonneg, f_rk_bounds⟩ := @EthierKurtz.ray_kernel_derivative_bounds d
  obtain ⟨f_rk_heat, f_measurableSet_Hs, f_continuous_Rf, f_mp_Rf, f_me_Rf, f_mass_even, f_mass_ray_inner⟩ := @EthierKurtz.ray_kernel_heat_equation_and_mass d
  haveI : ObliqueLib.IFacts d := ⟨f_contDiff_gK2_uncurry, f_continuous_gK1_uncurry, f_continuous_gK3_uncurry, f_sm_hN, f_inner_Rf, f_rK_pos, f_G_ray_le, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg, f_rk_bounds_gen, f_measurableSet_Hs, f_continuous_Rf, f_mp_Rf, f_me_Rf, f_mass_ray_inner⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fun {e} he b x => @ObliqueLib.sm_rk0 d _ e he b x)
  · exact (fun {e} he b x => @ObliqueLib.sm_rk1 d _ e he b x)
  · exact (fun {e} he b x => @ObliqueLib.sm_rk2 d _ e he b x)
  · exact (fun {e} he b x => @ObliqueLib.sm_rk3 d _ e he b x)
  · exact (fun {e} he {s} hs x S => @ObliqueLib.integrableOn_G_Rf d _ e he s hs x S)
  · exact (fun {e b} he hb {t} ht x => @ObliqueLib.integrableOn_rk0 d _ e b he hb t ht x)
  · exact (fun {e b} he hb {t} ht x => @ObliqueLib.mass_rk0 d _ e b he hb t ht x)
