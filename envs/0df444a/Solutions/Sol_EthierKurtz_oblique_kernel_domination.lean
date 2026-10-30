-- Prove2me | solution 1 for EthierKurtz.oblique_kernel_domination
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T16:42:01.800361+00:00
-- url     : https://prove2.me/submissions/f34d457c-9046-4d71-9652-ffa6247599b3

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_ray_kernel_derivative_bounds
import Theorems.Thm_EthierKurtz_ray_kernel_heat_equation_and_mass
import Theorems.Thm_EthierKurtz_oblique_kernel_bounds_heat_mass

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

lemma G_pos {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 < G d s z :=
  mul_pos (rpow_pos_of_pos (mul_pos pi_pos hs) _) (exp_pos _)

lemma G_nonneg {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 ≤ G d s z := (G_pos hs z).le

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

/-- Shifting the centre of a Gaussian by less than `1`. -/
lemma G_shift_le {d : ℕ} {s : ℝ} (hs : 0 < s) {x x₀ y : Eu d} (hx : ‖x - x₀‖ < 1) :
    G d s (x - y) ≤ rexp (1 / s) * 2 ^ ((d : ℝ) / 2) * G d (2 * s) (x₀ - y) := by
  unfold G
  have hn : (π * s) ^ (-((d : ℝ) / 2)) = 2 ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) := by
    rw [show π * (2 * s) = 2 * (π * s) by ring,
      mul_rpow (x := 2) (y := π * s) (by norm_num) (by positivity), ← mul_assoc,
      ← rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  have htri : ‖x₀ - y‖ ≤ 1 + ‖x - y‖ := by
    calc ‖x₀ - y‖ = ‖(x₀ - x) + (x - y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x₀ - x‖ + ‖x - y‖ := norm_add_le _ _
      _ ≤ 1 + ‖x - y‖ := by rw [norm_sub_rev]; linarith
  have he : -‖x - y‖ ^ 2 / s ≤ 1 / s + -‖x₀ - y‖ ^ 2 / (2 * s) := by
    rw [div_add_div _ _ hs.ne' (by positivity), div_le_div_iff₀ hs (by positivity)]
    have h0 : 0 ≤ ‖x₀ - y‖ := norm_nonneg _
    have hq : ‖x₀ - y‖ ^ 2 ≤ 2 + 2 * ‖x - y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x - y‖ - 1), mul_self_le_mul_self h0 htri]
    have := mul_le_mul_of_nonneg_left hq (le_of_lt (mul_pos hs hs))
    nlinarith [this]
  rw [hn]
  calc 2 ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) * rexp (-‖x - y‖ ^ 2 / s)
      ≤ 2 ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) *
          (rexp (1 / s) * rexp (-‖x₀ - y‖ ^ 2 / (2 * s))) := by
        rw [← Real.exp_add]; gcongr
    _ = _ := by ring

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

end OblDomA

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  wA_nonneg : 0 ≤ wA d
  whole_bounds : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), |wK d t x y| ≤ wA d * G d (4 * t) (x - y) ∧ ‖wK1 t x y‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK2 t x y‖ ≤ wA d * t ^ (-(1 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK3 t x y‖ ≤ wA d * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) (x - y)
  inner_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1) (x : Eu d), inner ℝ (Rf e x) e = -inner ℝ x e
  rK_pos : ∀ (b : Eu d), 0 < rK b
  rC_nonneg : ∀ (b : Eu d) (m σ : ℝ), 0 ≤ rC d b m σ
  rk_bounds_gen : ∀ {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t m : ℝ} (ht : 0 < t) (hm : 0 ≤ m) {x y : Eu d} (hxy : -m ≤ inner ℝ (x - Rf e y) e), |rk0 e b t x y| ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk1 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 : ℝ)) * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk2 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(3 / 2 : ℝ)) * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk3 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y)
  mp_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1), MeasurePreserving (Rf e) volume volume
  me_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1), MeasurableEmbedding (Rf e)
  oK_eq_smul : ∀ (e b : Eu d) (t : ℝ) (x y : Eu d), oK e b t x y = wK d t x y + wK d t x (Rf e y) - (2 : ℝ) • rk0 e b t x y

end IFk

export IFacts (wA_nonneg whole_bounds inner_Rf rK_pos rC_nonneg rk_bounds_gen mp_Rf me_Rf oK_eq_smul)

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

section OblDomA_dup

variable {d : ℕ}

noncomputable local instance instL2N14_dup (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S14_dup (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N14_dup (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S14_dup (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable [IFacts d]

lemma norm_comb_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A B C : F) :
    ‖A + B - (2 : ℝ) • C‖ ≤ ‖A‖ + ‖B‖ + 2 * ‖C‖ := by
  calc ‖A + B - (2 : ℝ) • C‖ ≤ ‖A + B‖ + ‖(2 : ℝ) • C‖ := norm_sub_le _ _
    _ ≤ ‖A‖ + ‖B‖ + 2 * ‖C‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [norm_add_le A B]

/-- Local domination of a kernel combination near `x₀` (for `KHyp.dom`). -/
lemma dom_core {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e b : Eu d}
    {t m P Q q1 q2 : ℝ} (ht : 0 < t) {x x₀ y : Eu d} (hx : ‖x - x₀‖ < 1) {A B C : F}
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq1P : q1 ≤ P) (hq2Q : q2 ≤ Q)
    (hA : ‖A‖ ≤ wA d * q1 * G d (4 * t) (x - y))
    (hB : ‖B‖ ≤ wA d * q1 * G d (4 * t) (x - Rf e y))
    (hC : ‖C‖ ≤ ‖b‖ * (2 * wA d) * q2 * rC d b m (4 * t) * G d (rK b * (4 * t)) (x - Rf e y)) :
    ‖A + B - (2 : ℝ) • C‖ ≤
      wA d * P * (rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2) * G d (2 * (4 * t)) (x₀ - y)) +
      wA d * P * (rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2) * G d (2 * (4 * t)) (x₀ - Rf e y)) +
      2 * (‖b‖ * (2 * wA d) * Q * rC d b m (4 * t) * (rexp (1 / (rK b * (4 * t))) *
        2 ^ ((d : ℝ) / 2) * G d (2 * (rK b * (4 * t))) (x₀ - Rf e y))) := by
  have hK := rK_pos b
  have s1 := G_shift_le (d := d) (by positivity : 0 < 4 * t) (y := y) hx
  have s2 := G_shift_le (d := d) (by positivity : 0 < 4 * t) (y := Rf e y) hx
  have s3 := G_shift_le (d := d) (by positivity : 0 < rK b * (4 * t)) (y := Rf e y) hx
  have hW := wA_nonneg (d := d)
  have hP : 0 ≤ P := hq1.trans hq1P
  have hQ : 0 ≤ Q := hq2.trans hq2Q
  have hrC := rC_nonneg (d := d) b m (4 * t)
  have hbW : 0 ≤ ‖b‖ * (2 * wA d) := mul_nonneg (norm_nonneg _) (by positivity)
  have g1 := G_nonneg (d := d) (by positivity : 0 < 4 * t) (x - y)
  have g2 := G_nonneg (d := d) (by positivity : 0 < 4 * t) (x - Rf e y)
  have g3 := G_nonneg (d := d) (by positivity : 0 < rK b * (4 * t)) (x - Rf e y)
  have a1 := hA.trans (mul_le_mul (mul_le_mul_of_nonneg_left hq1P hW) s1 g1 (mul_nonneg hW hP))
  have a2 := hB.trans (mul_le_mul (mul_le_mul_of_nonneg_left hq1P hW) s2 g2 (mul_nonneg hW hP))
  have a3 := hC.trans (mul_le_mul (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq2Q hbW) hrC) s3 g3 (mul_nonneg (mul_nonneg hbW hQ) hrC))
  exact (norm_comb_le A B C).trans (by linarith)

end OblDomA_dup

section OblDomB

variable {d : ℕ}

variable [IFacts d]

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

lemma oK_dom {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) :
    ∀ t, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, IntegrableOn F (Hs e) ∧
      ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Hs e, |oK e b t x y| ≤ F y ∧ ‖oK1 e b t x y‖ ≤ F y ∧
        ‖oK2 e b t x y‖ ≤ F y ∧ ‖oK3 e b t x y‖ ≤ F y := by
  intro t ht x₀
  have hK := rK_pos b
  set m := |inner ℝ x₀ e| + 1 with hm
  have hm0 : 0 ≤ m := by positivity
  have p1 := rpow_nonneg ht.le (-(1 / 2 : ℝ))
  have p2 := rpow_nonneg ht.le (-(1 : ℝ))
  have p3 := rpow_nonneg ht.le (-(3 / 2 : ℝ))
  have p4 := rpow_nonneg ht.le (-(2 : ℝ))
  set P := 1 + t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 : ℝ)) + t ^ (-(3 / 2 : ℝ))
  set Q := t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 : ℝ)) + t ^ (-(3 / 2 : ℝ)) + t ^ (-(2 : ℝ))
  set E1 := rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2)
  set E2 := rexp (1 / (rK b * (4 * t))) * 2 ^ ((d : ℝ) / 2)
  set R := ‖b‖ * (2 * wA d) * Q * rC d b m (4 * t)
  have i1 : Integrable (fun y => G d (2 * (4 * t)) (x₀ - y)) := integrable_G_sub (by positivity) x₀
  have i2 : Integrable (fun y => G d (2 * (4 * t)) (x₀ - Rf e y)) :=
    integrable_comp_Rf he (f := fun y => G d (2 * (4 * t)) (x₀ - y)) i1
  have i3 : Integrable (fun y => G d (2 * (rK b * (4 * t))) (x₀ - Rf e y)) :=
    integrable_comp_Rf he (f := fun y => G d (2 * (rK b * (4 * t))) (x₀ - y))
      (integrable_G_sub (by positivity) x₀)
  refine ⟨1, one_pos, fun y => wA d * P * (E1 * G d (2 * (4 * t)) (x₀ - y)) +
    wA d * P * (E1 * G d (2 * (4 * t)) (x₀ - Rf e y)) +
    2 * (R * (E2 * G d (2 * (rK b * (4 * t))) (x₀ - Rf e y))),
    ((((i1.const_mul E1).const_mul (wA d * P)).add ((i2.const_mul E1).const_mul (wA d * P))).add
      (((i3.const_mul E2).const_mul R).const_mul 2)).integrableOn, fun x hx y hy => ?_⟩
  have hx' : ‖x - x₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hxy : -m ≤ inner ℝ (x - Rf e y) e := by
    have hy' : 0 ≤ inner ℝ y e := hy
    have h1 : |inner ℝ (x - x₀) e| ≤ ‖x - x₀‖ := by
      have := abs_real_inner_le_norm (x - x₀) e; rwa [he, mul_one] at this
    have h2 : inner ℝ x e = inner ℝ x₀ e + inner ℝ (x - x₀) e := by
      rw [inner_sub_left]; ring
    rw [inner_sub_left, inner_Rf he, hm]
    linarith [neg_abs_le (inner ℝ x₀ e), neg_abs_le (inner ℝ (x - x₀) e)]
  obtain ⟨w0, w1, w2, w3⟩ := whole_bounds (d := d) ht x y
  obtain ⟨v0, v1, v2, v3⟩ := whole_bounds (d := d) ht x (Rf e y)
  obtain ⟨r0, r1, r2, r3⟩ := rk_bounds_gen he hb ht hm0 hxy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [oK_eq_smul, ← Real.norm_eq_abs]
    exact dom_core (F := ℝ) ht hx' zero_le_one p1 (by linarith) (by linarith)
      (by rw [Real.norm_eq_abs, mul_one]; exact w0) (by rw [Real.norm_eq_abs, mul_one]; exact v0)
      (by rw [Real.norm_eq_abs]; exact r0)
  · exact dom_core ht hx' p1 p2 (by linarith) (by linarith) w1 v1 r1
  · exact dom_core ht hx' p2 p3 (by linarith) (by linarith) w2 v2 r2
  · exact dom_core ht hx' p3 p4 (by linarith) (by linarith) w3 v3 r3

end OblDomB

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
  let oK : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK t x y + wK t x (Rf e y) - 2 * rk0 e b t x y);
  let oK1 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK1 t x y + wK1 t x (Rf e y) - (2 : ℝ) • rk1 e b t x y);
  let oK2 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK2 t x y + wK2 t x (Rf e y) - (2 : ℝ) • rk2 e b t x y);
  let oK3 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (wK3 t x y + wK3 t x (Rf e y) - (2 : ℝ) • rk3 e b t x y);
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0), ∀ t, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, IntegrableOn F (Hs e) ∧ ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Hs e, |oK e b t x y| ≤ F y ∧ ‖oK1 e b t x y‖ ≤ F y ∧ ‖oK2 e b t x y‖ ≤ F y ∧ ‖oK3 e b t x y‖ ≤ F y) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN wK wK1 wK2 wK3 Rf gK4 eb1 eb2 eb3 rP0 rP1 rP2 rP3 rk0 rk1 rk2 rk3 Hs oK oK1 oK2 oK3
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_continuous_rP2, f_continuous_rP1, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg, f_rk_d0, f_rk_d1, f_rk_d2, f_rk_bounds_gen, f_rA_nonneg, f_rk_bounds⟩ := @EthierKurtz.ray_kernel_derivative_bounds d
  obtain ⟨f_rk_heat, f_measurableSet_Hs, f_continuous_Rf, f_mp_Rf, f_me_Rf, f_mass_even, f_mass_ray_inner⟩ := @EthierKurtz.ray_kernel_heat_equation_and_mass d
  obtain ⟨f_oA_nonneg, f_convex_Hs, f_oK_eq_smul, f_oK_bounds, f_oK_heat, f_oK_mass⟩ := @EthierKurtz.oblique_kernel_bounds_heat_mass d
  haveI : ObliqueLib.IFacts d := ⟨f_wA_nonneg, f_whole_bounds, f_inner_Rf, f_rK_pos, f_rC_nonneg, f_rk_bounds_gen, f_mp_Rf, f_me_Rf, f_oK_eq_smul⟩
  exact (fun {e b} he hb => @ObliqueLib.oK_dom d _ e b he hb)
