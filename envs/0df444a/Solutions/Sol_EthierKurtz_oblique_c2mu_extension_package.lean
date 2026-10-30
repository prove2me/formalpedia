-- Prove2me | solution 1 for EthierKurtz.oblique_c2mu_extension_package
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T15:19:25.468107+00:00
-- url     : https://prove2.me/submissions/47ab6a8a-9ae3-479d-b972-1b3034085bac

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_heat_kernel_smoothing_estimates
import Theorems.Thm_EthierKurtz_heat_extension_c1mu_properties
import Theorems.Thm_EthierKurtz_heat_extension_holder_estimates

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

/-- Gaussian moment constant. -/
noncomputable def gm (d : ℕ) : ℝ := 1 + 2 * 2 ^ ((d : ℝ) / 2)

lemma gm_pos (d : ℕ) : 0 < gm d := by unfold gm; positivity

/-- Shortcut instances: without them `Norm (E →L E →L E →L ℝ)` fails to synthesize. -/
noncomputable local instance instL2N (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section KHypDef

/-- Hypotheses on a kernel family `K t x y` (time `t > 0`) with `x`-derivatives `K1 K2 K3`
and Gaussian bounds on the convex set `S`. -/
@[reducible] def KHyp (d : ℕ) (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ)
    (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ))
    (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)) (A c : ℝ) : Prop :=
  (0 ≤ A) ∧
    (0 < c) ∧
    (MeasurableSet S) ∧
    (Convex ℝ S) ∧
    (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
    (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
    (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
    (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G d (c * t) (x - y)) ∧
    (∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K p.1 x p.2)) ∧
    (∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K1 p.1 x p.2)) ∧
    (∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K2 p.1 x p.2)) ∧
    (∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2)) ∧
    (∀ t, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, IntegrableOn F S ∧ ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧ ‖K3 t x y‖ ≤ F y) ∧
    (∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => K t x y) ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
    (∀ t, 0 < t → ∀ x, ∫ y in S, K t x y = 1)

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}

theorem KHyp.hA (h : KHyp d S K K1 K2 K3 A c) : 0 ≤ A := h.1

theorem KHyp.hc (h : KHyp d S K K1 K2 K3 A c) : 0 < c := h.2.1

theorem KHyp.b0 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.1

theorem KHyp.b1 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.1

end KHypDef

/-- `h` is bounded by `M0` and `μ`-Hölder with constant `Hh` on `S`. -/
def HolderOnS {d : ℕ} (S : Set (Eu d)) (μ M0 Hh : ℝ) (h : Eu d → ℝ) : Prop :=
  0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ

/-- Trace of a bilinear form in the standard basis (twice the generator `Δ/2` acts as `lap2/2`). -/
noncomputable def lap2 {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

section C1Hdef

/-- `ψ` is bounded, differentiable with bounded, continuous, `μ`-Hölder derivative `ψ1`. -/
@[reducible] def C1H (d : ℕ) (μ M0 M1 H : ℝ) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) : Prop :=
  (∀ y, HasFDerivAt ψ (ψ1 y) y) ∧ Continuous ψ1 ∧ (∀ y, |ψ y| ≤ M0) ∧ (∀ y, ‖ψ1 y‖ ≤ M1) ∧
    (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H

variable {d : ℕ} {μ M0 M1 H : ℝ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)}

theorem C1H.hd (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, HasFDerivAt ψ (ψ1 y) y := hC.1

theorem C1H.cont (hC : C1H d μ M0 M1 H ψ ψ1) : Continuous ψ1 := hC.2.1

theorem C1H.b0 (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, |ψ y| ≤ M0 := hC.2.2.1

theorem C1H.b1 (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, ‖ψ1 y‖ ≤ M1 := hC.2.2.2.1

theorem C1H.hH (hC : C1H d μ M0 M1 H ψ ψ1) : 0 ≤ H := hC.2.2.2.2.2

end C1Hdef

section KernelInt

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}

/-- Space integrals of the kernel and its derivatives against `h`. -/
noncomputable def kw0 (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ) (h : Eu d → ℝ) (t : ℝ)
    (x : Eu d) : ℝ := ∫ y in S, h y • K t x y

noncomputable def kw1 (S : Set (Eu d)) (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)) (h : Eu d → ℝ)
    (t : ℝ) (x : Eu d) : Eu d →L[ℝ] ℝ := ∫ y in S, h y • K1 t x y

noncomputable def kw2 (S : Set (Eu d)) (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (h : Eu d → ℝ) (t : ℝ) (x : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ := ∫ y in S, h y • K2 t x y

noncomputable def kw3 (S : Set (Eu d))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (h : Eu d → ℝ) (t : ℝ) (x : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ y in S, h y • K3 t x y

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

section KTime

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

/-- `lap2` as a continuous linear map. -/
noncomputable def lap2L (d : ℕ) : (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (Eu d →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ)))

end KTime

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

section Transfer

variable {d : ℕ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {M0 M1 : ℝ}

end Transfer

section WholeAPI

variable {d : ℕ} {h : Eu d → ℝ} {μ M0 Hh : ℝ}

noncomputable local instance instL2NW (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2SW (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end WholeAPI

section Ext1

variable {d : ℕ}

/-- Heat extension with value `h` at time `0`. -/
noncomputable def Wb (h : Eu d → ℝ) (s : ℝ) (x : Eu d) : ℝ :=
  if 0 < s then kw0 univ (wK d) h s x else h x

/-- Boundary profile: `FE e ψ y = Wb ψ (⟪y,e⟫²) y`. -/
noncomputable def FE (e : Eu d) (ψ : Eu d → ℝ) (y : Eu d) : ℝ := Wb ψ (inner ℝ y e ^ 2) y

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

end Ext1

section Ext2

variable {d : ℕ}

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

/-- Derivative of the profile off the plane. -/
noncomputable def DFE (e : Eu d) (ψ : Eu d → ℝ) (y : Eu d) : Eu d →L[ℝ] ℝ :=
  (inner ℝ y e * lap2 (kw2 univ wK2 ψ (inner ℝ y e ^ 2) y)) • innerSL ℝ e
    + kw1 univ wK1 ψ (inner ℝ y e ^ 2) y

end Ext2

section Ext3

variable {d : ℕ}

/-- Orthogonal projection onto `e⊥` (for a unit vector `e`), as a CLM. -/
noncomputable def PeL (e : Eu d) : Eu d →L[ℝ] Eu d :=
  ContinuousLinearMap.id ℝ (Eu d) - (innerSL ℝ e).smulRight e

/-- `Q e ψ p b = ∫_0^b FE e ψ (P p + τ e) dτ`. -/
noncomputable def QE (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (b : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..b, FE e ψ (PeL e p + τ • e)

/-- The extension. -/
noncomputable def EXT (e : Eu d) (ψ : Eu d → ℝ) (x : Eu d) : ℝ := QE e ψ x (inner ℝ x e)

/-- `p`-derivative of `QE`. -/
noncomputable def DQE (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (b : ℝ) : Eu d →L[ℝ] ℝ :=
  ∫ τ in (0 : ℝ)..b, (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

end Ext3

section Ext4

variable {d : ℕ}

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

/-- The integrand of `DQE`. -/
noncomputable def DQI (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (τ : ℝ) : Eu d →L[ℝ] ℝ :=
  (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)

/-- Derivative of the extension. -/
noncomputable def DEXT (e : Eu d) (ψ : Eu d → ℝ) (x : Eu d) : Eu d →L[ℝ] ℝ :=
  DQE e ψ x (inner ℝ x e) + FE e ψ x • innerSL ℝ e

end Ext4

section Ext5

variable {d : ℕ}

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

/-- The constant of the `τ^(μ-1)` bound. -/
noncomputable def KB (d : ℕ) (μ H : ℝ) : ℝ := wA d * H * gm d * 4 ^ (μ / 2)

/-- `p`-derivative of `DQI` (for `τ ≠ 0`). -/
noncomputable def D2QI (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (τ : ℝ) :
    Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)).comp
    ((kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e))

/-- Second `p`-derivative of `QE`. -/
noncomputable def D2QE (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (b : ℝ) :
    Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ τ in (0 : ℝ)..b, D2QI e ψ p τ

/-- Second derivative of the extension (open side). -/
noncomputable def D2EXT (e : Eu d) (ψ : Eu d → ℝ) (x : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  D2QE e ψ x (inner ℝ x e) + (innerSL ℝ e).smulRight (DQI e ψ x (inner ℝ x e))
    + (DFE e ψ x).smulRight (innerSL ℝ e)

end Ext5

section Hol1

variable {d : ℕ} {h : Eu d → ℝ} {μ M Hh : ℝ}

/-- Constant of the time-Hölder bound. -/
noncomputable def cTm (d : ℕ) (μ : ℝ) : ℝ := (d / μ + 1) * wA d * gm d * 4 ^ (μ / 2)

/-- Constant of the Hölder bound of the parabolic extension. -/
noncomputable def cH (d : ℕ) (μ : ℝ) : ℝ :=
  (2 + 2 ^ μ) * wA d * gm d * 4 ^ (μ / 2) + 1 + cTm d μ

end Hol1

section Hol2

variable {d : ℕ} {h : Eu d → ℝ} {μ M Hh : ℝ}

/-- `wA gm 4^(μ/2) Hh`. -/
noncomputable def KH1 (d : ℕ) (μ Hh : ℝ) : ℝ := wA d * gm d * 4 ^ (μ / 2) * Hh

/-- The normal-derivative term. -/
noncomputable def TK (e : Eu d) (h : Eu d → ℝ) (x : Eu d) : Eu d →L[ℝ] ℝ :=
  inner ℝ x e • kw1 univ wK1 h (inner ℝ x e ^ 2) x

/-- Constant of the Hölder bound of `TK` (per unit `Hh`). -/
noncomputable def cTK (d : ℕ) (μ : ℝ) : ℝ :=
  5 * wA d * gm d * 4 ^ (μ / 2) + 32 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ

end Hol2

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  wA_nonneg : 0 ≤ wA d
  kw1_trans : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x v : Eu d), kw1 univ wK1 ψ t x v = kw0 univ (wK d) (fun y => ψ1 y v) t x
  kw3_trans : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x w u v : Eu d), kw3 univ wK3 ψ t x w u v = kw2 univ wK2 (fun y => ψ1 y v) t x w u
  wh_hasFDerivAt_kw2 : ∀ {h : Eu d → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (Eu d)), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw2 univ wK2 h t) (kw3 univ wK3 h t x) x
  C1H_continuous : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1), Continuous ψ
  C1H_holV : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (v : Eu d), HolderOnS univ μ (M1 * ‖v‖) (H * ‖v‖) (fun y => ψ1 y v)
  C1H_measV : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (v : Eu d), AEStronglyMeasurable (fun y => ψ1 y v) (volume.restrict (univ : Set (Eu d)))
  C1H_lap2_kw2_eq : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) {s : ℝ} (hs : 0 < s) (y : Eu d), lap2 (kw2 univ wK2 ψ s y) = ∑ i : Fin d, kw1 univ wK1 (fun z => ψ1 z (EuclideanSpace.single i 1)) s y (EuclideanSpace.single i 1)
  PeL_add_inner : ∀ (e x : Eu d), PeL e x + inner ℝ x e • e = x
  C1H_EXT_strict : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1) (x₀ : Eu d), HasStrictFDerivAt (EXT e ψ) (DEXT e ψ x₀) x₀
  C1H_DEXT_continuous : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1), Continuous (DEXT e ψ)
  EXT_plane : ∀ {ψ : Eu d → ℝ} {e x : Eu d} (hx : inner ℝ x e = 0), EXT e ψ x = 0
  DEXT_plane : ∀ {ψ : Eu d → ℝ} {e x : Eu d} (hx : inner ℝ x e = 0), DEXT e ψ x = ψ x • innerSL ℝ e
  C1H_KB_nonneg : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1), 0 ≤ KB d μ H
  norm_flipP_le : ∀ (e : Eu d), ‖(ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)‖ ≤ ‖PeL e‖
  C1H_D2QI_le : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {e : Eu d} {τ : ℝ} (hτ : 0 < τ) (p : Eu d), ‖D2QI e ψ p τ‖ ≤ ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1)
  C1H_D2QI_ii : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (e p : Eu d) {c : ℝ} (hc : 0 ≤ c), IntervalIntegrable (fun τ => D2QI e ψ p τ) volume 0 c
  C1H_DEXT_hasFDerivAt : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d} {x₀ : Eu d} (hx₀ : 0 < inner ℝ x₀ e), HasFDerivAt (DEXT e ψ) (D2EXT e ψ x₀) x₀
  FE_hol : ∀ {h : Eu d → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d} (he : ‖e‖ = 1) (x x' : Eu d), |FE e h x - FE e h x'| ≤ cH d μ * Hh * ‖x - x'‖ ^ μ
  KH1_nonneg : ∀ {μ Hh : ℝ} (hH : 0 ≤ Hh), 0 ≤ KH1 d μ Hh
  kw2h_tau_le : ∀ {h : Eu d → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {a : ℝ} (ha : 0 < a) (y : Eu d), ‖kw2 univ wK2 h (a ^ 2) y‖ ≤ KH1 d μ Hh * a ^ (μ - 2)
  TK_hol : ∀ {h : Eu d → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d} (he : ‖e‖ = 1) (x x' : Eu d), ‖TK e h x - TK e h x'‖ ≤ cTK d μ * Hh * ‖x - x'‖ ^ μ

end IFk

export IFacts (wA_nonneg kw1_trans kw3_trans wh_hasFDerivAt_kw2 PeL_add_inner EXT_plane DEXT_plane norm_flipP_le FE_hol KH1_nonneg kw2h_tau_le TK_hol)

theorem C1H.continuous {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1), Continuous ψ := IFacts.C1H_continuous

theorem C1H.holV {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (v : Eu d), HolderOnS univ μ (M1 * ‖v‖) (H * ‖v‖) (fun y => ψ1 y v) := IFacts.C1H_holV

theorem C1H.measV {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (v : Eu d), AEStronglyMeasurable (fun y => ψ1 y v) (volume.restrict (univ : Set (Eu d))) := IFacts.C1H_measV

theorem C1H.lap2_kw2_eq {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) {s : ℝ} (hs : 0 < s) (y : Eu d), lap2 (kw2 univ wK2 ψ s y) = ∑ i : Fin d, kw1 univ wK1 (fun z => ψ1 z (EuclideanSpace.single i 1)) s y (EuclideanSpace.single i 1) := IFacts.C1H_lap2_kw2_eq

theorem C1H.EXT_strict {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1) (x₀ : Eu d), HasStrictFDerivAt (EXT e ψ) (DEXT e ψ x₀) x₀ := IFacts.C1H_EXT_strict

theorem C1H.DEXT_continuous {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1), Continuous (DEXT e ψ) := IFacts.C1H_DEXT_continuous

theorem C1H.KB_nonneg {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1), 0 ≤ KB d μ H := IFacts.C1H_KB_nonneg

theorem C1H.D2QI_le {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {e : Eu d} {τ : ℝ} (hτ : 0 < τ) (p : Eu d), ‖D2QI e ψ p τ‖ ≤ ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1) := IFacts.C1H_D2QI_le

theorem C1H.D2QI_ii {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (e p : Eu d) {c : ℝ} (hc : 0 ≤ c), IntervalIntegrable (fun τ => D2QI e ψ p τ) volume 0 c := IFacts.C1H_D2QI_ii

theorem C1H.DEXT_hasFDerivAt {d : ℕ} [IFacts d] : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d} {x₀ : Eu d} (hx₀ : 0 < inner ℝ x₀ e), HasFDerivAt (DEXT e ψ) (D2EXT e ψ x₀) x₀ := IFacts.C1H_DEXT_hasFDerivAt

section Ext5_dup

variable {d : ℕ}

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

variable [IFacts d]

lemma rpow_ii {μ : ℝ} (hμ0 : 0 < μ) (C a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => C * τ ^ (μ - 1)) volume a b :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C

end Ext5_dup

section Hol1_dup

variable {d : ℕ} {h : Eu d → ℝ} {μ M Hh : ℝ}

variable [IFacts d]

lemma abs_rpow_sub_le {a b μ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    |a ^ μ - b ^ μ| ≤ |a - b| ^ μ := by
  rcases le_total b a with h | h
  · have h1 := Real.rpow_add_le_add_rpow hb (sub_nonneg.mpr h) hμ0 hμ1
    rw [add_sub_cancel] at h1
    rw [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hb h hμ0)), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith
  · have h1 := Real.rpow_add_le_add_rpow ha (sub_nonneg.mpr h) hμ0 hμ1
    rw [add_sub_cancel] at h1
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow ha h hμ0)), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr h)]
    linarith

end Hol1_dup

section Hol3

variable {d : ℕ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

variable [IFacts d]

lemma C1H.kw3_tau_le (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {τ : ℝ} (hτ : 0 < τ) (y : Eu d) :
    ‖kw3 univ wK3 ψ (τ ^ 2) y‖ ≤ KH1 d μ H * τ ^ (μ - 2) := by
  have hK0 : 0 ≤ KH1 d μ H * τ ^ (μ - 2) := mul_nonneg (KH1_nonneg hC.hH) (rpow_nonneg hτ.le _)
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK0 (norm_nonneg w)) fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hK0 (norm_nonneg w)) (norm_nonneg u)) fun v => ?_
  rw [kw3_trans hC.hd hC.cont hC.b0 hC.b1 (by positivity) y w u v]
  have h1 := kw2h_tau_le (hC.holV v) (hC.measV v) hμ0 hμ2 hτ y
  calc ‖kw2 univ wK2 (fun y => ψ1 y v) (τ ^ 2) y w u‖
      ≤ ‖kw2 univ wK2 (fun y => ψ1 y v) (τ ^ 2) y‖ * ‖w‖ * ‖u‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ KH1 d μ (H * ‖v‖) * τ ^ (μ - 2) * ‖w‖ * ‖u‖ := by gcongr
    _ = KH1 d μ H * τ ^ (μ - 2) * ‖w‖ * ‖u‖ * ‖v‖ := by unfold KH1; ring

lemma C1H.kw2_lip_tau (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {τ : ℝ} (hτ : 0 < τ) (y y' : Eu d) :
    ‖kw2 univ wK2 ψ (τ ^ 2) y' - kw2 univ wK2 ψ (τ ^ 2) y‖ ≤
      KH1 d μ H * τ ^ (μ - 2) * ‖y' - y‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (wh_hasFDerivAt_kw2 hC.continuous.aestronglyMeasurable
      (fun y _ => hC.b0 y) (by positivity) z).hasFDerivWithinAt)
    (fun z _ => hC.kw3_tau_le hμ0 hμ2 hτ z) convex_univ (mem_univ y) (mem_univ y')

lemma D2QI_sub_le (e : Eu d) (ψ : Eu d → ℝ) (p p' : Eu d) (τ : ℝ) :
    ‖D2QI e ψ p' τ - D2QI e ψ p τ‖ ≤ ‖PeL e‖ ^ 2 *
      ‖kw2 univ wK2 ψ (τ ^ 2) (PeL e p' + τ • e) - kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)‖ := by
  have e1 : D2QI e ψ p' τ - D2QI e ψ p τ =
      ((ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)).comp
        ((kw2 univ wK2 ψ (τ ^ 2) (PeL e p' + τ • e) -
          kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)) := by
    unfold D2QI; rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [e1]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h2 := ContinuousLinearMap.opNorm_comp_le
    (kw2 univ wK2 ψ (τ ^ 2) (PeL e p' + τ • e) - kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e))
    (PeL e)
  calc _ ≤ ‖PeL e‖ * (‖kw2 univ wK2 ψ (τ ^ 2) (PeL e p' + τ • e) -
        kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)‖ * ‖PeL e‖) :=
        mul_le_mul (norm_flipP_le e) h2 (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

lemma C1H.D2QI_sub_le_far (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {e : Eu d} {τ : ℝ} (hτ : 0 < τ) (p p' : Eu d) :
    ‖D2QI e ψ p' τ - D2QI e ψ p τ‖ ≤
      ‖PeL e‖ ^ 3 * KH1 d μ H * ‖p' - p‖ * τ ^ (μ - 2) := by
  refine (D2QI_sub_le e ψ p p' τ).trans ?_
  have h1 := hC.kw2_lip_tau hμ0 hμ2 hτ (PeL e p + τ • e) (PeL e p' + τ • e)
  have h2 : ‖(PeL e p' + τ • e) - (PeL e p + τ • e)‖ ≤ ‖PeL e‖ * ‖p' - p‖ := by
    rw [add_sub_add_right_eq_sub, ← map_sub]; exact (PeL e).le_opNorm _
  have hK : 0 ≤ KH1 d μ H * τ ^ (μ - 2) := mul_nonneg (KH1_nonneg hC.hH) (rpow_nonneg hτ.le _)
  calc ‖PeL e‖ ^ 2 * ‖kw2 univ wK2 ψ (τ ^ 2) (PeL e p' + τ • e) -
        kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)‖
      ≤ ‖PeL e‖ ^ 2 * (KH1 d μ H * τ ^ (μ - 2) * (‖PeL e‖ * ‖p' - p‖)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hK)) (sq_nonneg _)
    _ = _ := by ring

lemma C1H.D2QI_sub_le_near (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {e : Eu d} {τ : ℝ} (hτ : 0 < τ) (p p' : Eu d) :
    ‖D2QI e ψ p' τ - D2QI e ψ p τ‖ ≤ 2 * ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1) := by
  have h1 := hC.D2QI_le hμ0 hμ2 (e := e) hτ p
  have h2 := hC.D2QI_le hμ0 hμ2 (e := e) hτ p'
  have := norm_sub_le (D2QI e ψ p' τ) (D2QI e ψ p τ)
  linarith

/-- Constant of the `p`-Hölder bound of `D2QE`. -/
noncomputable def cQp (d : ℕ) (μ H : ℝ) (e : Eu d) : ℝ :=
  ‖PeL e‖ ^ 2 * (2 * KB d μ H / μ + ‖PeL e‖ * KH1 d μ H / (1 - μ))

lemma C1H.D2QE_hol_p (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ < 1) {e : Eu d}
    {b : ℝ} (hb : 0 ≤ b) (p p' : Eu d) :
    ‖D2QE e ψ p' b - D2QE e ψ p b‖ ≤ cQp d μ H e * ‖p' - p‖ ^ μ := by
  have hμ2 : μ ≤ 2 := by linarith
  have hKB := hC.KB_nonneg
  have hK1 := KH1_nonneg (d := d) (μ := μ) hC.hH
  have hP := norm_nonneg (PeL e)
  have hδ0 : 0 ≤ ‖p' - p‖ := norm_nonneg _
  have hc1 : 0 ≤ 2 * KB d μ H / μ := div_nonneg (by linarith) hμ0.le
  have hc2 : 0 ≤ ‖PeL e‖ * KH1 d μ H / (1 - μ) :=
    div_nonneg (mul_nonneg hP hK1) (by linarith)
  have hcQ : 0 ≤ cQp d μ H e := mul_nonneg (sq_nonneg _) (add_nonneg hc1 hc2)
  have hii : ∀ q : Eu d, ∀ c, 0 ≤ c → IntervalIntegrable (fun τ => D2QI e ψ q τ) volume 0 c :=
    fun q c hc => hC.D2QI_ii hμ0 hμ2 e q hc
  have hdiff : D2QE e ψ p' b - D2QE e ψ p b =
      ∫ τ in (0 : ℝ)..b, (D2QI e ψ p' τ - D2QI e ψ p τ) := by
    unfold D2QE; rw [intervalIntegral.integral_sub (hii p' b hb) (hii p b hb)]
  rw [hdiff]
  -- the near bound integrates to `2‖P‖²KB c^μ/μ`
  have hnearI : ∀ c, 0 ≤ c →
      ‖∫ τ in (0 : ℝ)..c, (D2QI e ψ p' τ - D2QI e ψ p τ)‖ ≤
        2 * ‖PeL e‖ ^ 2 * KB d μ H * (c ^ μ / μ) := by
    intro c hc
    have hI : IntervalIntegrable (fun τ : ℝ => 2 * ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1))
        volume 0 c := rpow_ii hμ0 _ _ _
    refine (intervalIntegral.norm_integral_le_of_norm_le hc
      (Eventually.of_forall fun τ hτ => hC.D2QI_sub_le_near hμ0.le hμ2 hτ.1 p p') hI).trans
      (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    rw [show μ - 1 + 1 = μ by ring, zero_rpow hμ0.ne', sub_zero]
  rcases le_total b ‖p' - p‖ with hbδ | hδb
  · refine (hnearI b hb).trans ?_
    have h1 : b ^ μ ≤ ‖p' - p‖ ^ μ := rpow_le_rpow hb hbδ hμ0.le
    unfold cQp
    have h2 : 2 * ‖PeL e‖ ^ 2 * KB d μ H * (b ^ μ / μ) ≤
        2 * ‖PeL e‖ ^ 2 * KB d μ H * (‖p' - p‖ ^ μ / μ) := by
      gcongr
    have h3 : 0 ≤ ‖PeL e‖ ^ 2 * (‖PeL e‖ * KH1 d μ H / (1 - μ)) * ‖p' - p‖ ^ μ :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hc2) (rpow_nonneg hδ0 _)
    have e3 : ‖PeL e‖ ^ 2 * (2 * KB d μ H / μ + ‖PeL e‖ * KH1 d μ H / (1 - μ)) * ‖p' - p‖ ^ μ =
        2 * ‖PeL e‖ ^ 2 * KB d μ H * (‖p' - p‖ ^ μ / μ) +
        ‖PeL e‖ ^ 2 * (‖PeL e‖ * KH1 d μ H / (1 - μ)) * ‖p' - p‖ ^ μ := by ring
    rw [e3]; linarith
  · rcases hδ0.lt_or_eq with hδpos | hδz
    · set δ := ‖p' - p‖ with hδdef
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (((hii p' δ hδ0).sub (hii p δ hδ0)))
        (((hii p' b hb).sub (hii p b hb)).mono_set (by
          rw [uIcc_of_le hδb, uIcc_of_le hb]; exact Icc_subset_Icc hδ0 le_rfl))
      rw [← hsplit]
      have h1 := hnearI δ hδ0
      have hI2 : IntervalIntegrable (fun τ : ℝ => ‖PeL e‖ ^ 3 * KH1 d μ H * δ * τ ^ (μ - 2))
          volume δ b :=
        (intervalIntegral.intervalIntegrable_rpow (Or.inr (by
          rw [uIcc_of_le hδb]; intro h0; exact absurd h0.1 (not_le.mpr hδpos)))).const_mul _
      have h2 : ‖∫ τ in δ..b, (D2QI e ψ p' τ - D2QI e ψ p τ)‖ ≤
          ∫ τ in δ..b, ‖PeL e‖ ^ 3 * KH1 d μ H * δ * τ ^ (μ - 2) :=
        intervalIntegral.norm_integral_le_of_norm_le hδb
          (Eventually.of_forall fun τ hτ =>
            hC.D2QI_sub_le_far hμ0.le hμ2 (lt_trans hδpos hτ.1) p p') hI2
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by intro h; linarith, by
          rw [uIcc_of_le hδb]; intro h0; exact absurd h0.1 (not_le.mpr hδpos)⟩)] at h2
      rw [show μ - 2 + 1 = μ - 1 by ring] at h2
      have hb1 : 0 ≤ b ^ (μ - 1) := rpow_nonneg hb _
      have hdd : δ * ((b ^ (μ - 1) - δ ^ (μ - 1)) / (μ - 1)) ≤ δ ^ μ / (1 - μ) := by
        have hne : (μ - 1) ≠ 0 := by intro h; linarith
        have hne2 : (1 - μ) ≠ 0 := by intro h; linarith
        have e4 : δ * ((b ^ (μ - 1) - δ ^ (μ - 1)) / (μ - 1)) =
            (δ * δ ^ (μ - 1) - δ * b ^ (μ - 1)) / (1 - μ) := by
          field_simp; ring
        have e5 : δ * δ ^ (μ - 1) = δ ^ μ := by
          rw [mul_comm, ← Real.rpow_add_one hδpos.ne']; ring_nf
        rw [e4, e5]
        refine div_le_div_of_nonneg_right ?_ (by linarith)
        have := mul_nonneg hδ0 hb1; linarith
      have hfin := norm_add_le (∫ τ in (0 : ℝ)..δ, (D2QI e ψ p' τ - D2QI e ψ p τ))
        (∫ τ in δ..b, (D2QI e ψ p' τ - D2QI e ψ p τ))
      have hK3 : 0 ≤ ‖PeL e‖ ^ 3 * KH1 d μ H := mul_nonneg (pow_nonneg hP 3) hK1
      have h2' : ‖∫ τ in δ..b, (D2QI e ψ p' τ - D2QI e ψ p τ)‖ ≤
          ‖PeL e‖ ^ 3 * KH1 d μ H * (δ ^ μ / (1 - μ)) := by
        refine h2.trans ?_
        calc ‖PeL e‖ ^ 3 * KH1 d μ H * δ * ((b ^ (μ - 1) - δ ^ (μ - 1)) / (μ - 1))
            = ‖PeL e‖ ^ 3 * KH1 d μ H * (δ * ((b ^ (μ - 1) - δ ^ (μ - 1)) / (μ - 1))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hdd hK3
      unfold cQp
      have e6 : ‖PeL e‖ ^ 2 * (2 * KB d μ H / μ + ‖PeL e‖ * KH1 d μ H / (1 - μ)) * δ ^ μ =
          2 * ‖PeL e‖ ^ 2 * KB d μ H * (δ ^ μ / μ) +
          ‖PeL e‖ ^ 3 * KH1 d μ H * (δ ^ μ / (1 - μ)) := by ring
      rw [e6]; linarith
    · have hpp : p' = p := sub_eq_zero.mp (norm_eq_zero.mp hδz.symm)
      rw [hpp]
      have h0 : ∫ τ in (0 : ℝ)..b, (D2QI e ψ p τ - D2QI e ψ p τ) = 0 := by simp
      rw [h0, norm_zero]; exact mul_nonneg hcQ (rpow_nonneg (norm_nonneg _) _)

lemma C1H.D2QE_hol_b (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d}
    (p : Eu d) {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    ‖D2QE e ψ p b' - D2QE e ψ p b‖ ≤ ‖PeL e‖ ^ 2 * KB d μ H / μ * |b' - b| ^ μ := by
  have hμ2 : μ ≤ 2 := by linarith
  have hC0 : 0 ≤ ‖PeL e‖ ^ 2 * KB d μ H := mul_nonneg (sq_nonneg _) hC.KB_nonneg
  have key : ∀ c c', 0 ≤ c → c ≤ c' →
      ‖D2QE e ψ p c' - D2QE e ψ p c‖ ≤ ‖PeL e‖ ^ 2 * KB d μ H / μ * (c' - c) ^ μ := by
    intro c c' hc hcc
    have hc' : 0 ≤ c' := hc.trans hcc
    unfold D2QE
    rw [intervalIntegral.integral_interval_sub_left (hC.D2QI_ii hμ0 hμ2 e p hc')
      (hC.D2QI_ii hμ0 hμ2 e p hc)]
    have hI : IntervalIntegrable (fun τ : ℝ => ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1))
        volume c c' := rpow_ii hμ0 _ _ _
    refine (intervalIntegral.norm_integral_le_of_norm_le hcc
      (Eventually.of_forall fun τ hτ => hC.D2QI_le hμ0.le hμ2
        (lt_of_le_of_lt hc hτ.1) p) hI).trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      show μ - 1 + 1 = μ by ring]
    have h1 := abs_rpow_sub_le hc' hc hμ0.le hμ1
    rw [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hc hcc hμ0.le)),
      abs_of_nonneg (sub_nonneg.mpr hcc)] at h1
    calc ‖PeL e‖ ^ 2 * KB d μ H * ((c' ^ μ - c ^ μ) / μ)
        = ‖PeL e‖ ^ 2 * KB d μ H / μ * (c' ^ μ - c ^ μ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (div_nonneg hC0 hμ0.le)
  rcases le_total b b' with hh | hh
  · rw [abs_of_nonneg (sub_nonneg.mpr hh)]; exact key b b' hb hh
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hh)]; exact key b' b hb' hh

/-- **Hölder continuity of the `D2QE` part of the second derivative** on `⟪·,e⟫ ≥ 0`. -/
lemma C1H.D2QE_hol (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ < 1) {e : Eu d}
    (he : ‖e‖ = 1) {x x' : Eu d} (hx : 0 ≤ inner ℝ x e) (hx' : 0 ≤ inner ℝ x' e) :
    ‖D2QE e ψ x' (inner ℝ x' e) - D2QE e ψ x (inner ℝ x e)‖ ≤
      (cQp d μ H e + ‖PeL e‖ ^ 2 * KB d μ H / μ) * ‖x' - x‖ ^ μ := by
  have h1 := hC.D2QE_hol_p hμ0 hμ1 (e := e) hx' x x'
  have h2 := hC.D2QE_hol_b hμ0 hμ1.le (e := e) x hx hx'
  have h3 : |inner ℝ x' e - inner ℝ x e| ^ μ ≤ ‖x' - x‖ ^ μ := by
    refine rpow_le_rpow (abs_nonneg _) ?_ hμ0.le
    rw [← inner_sub_left]; refine (abs_real_inner_le_norm _ _).trans ?_; rw [he, mul_one]
  have hC0 : 0 ≤ ‖PeL e‖ ^ 2 * KB d μ H / μ :=
    div_nonneg (mul_nonneg (sq_nonneg _) hC.KB_nonneg) hμ0.le
  have h4 := mul_le_mul_of_nonneg_left h3 hC0
  have e1 : D2QE e ψ x' (inner ℝ x' e) - D2QE e ψ x (inner ℝ x e) =
      (D2QE e ψ x' (inner ℝ x' e) - D2QE e ψ x (inner ℝ x' e)) +
      (D2QE e ψ x (inner ℝ x' e) - D2QE e ψ x (inner ℝ x e)) := by abel
  rw [e1]
  have := norm_add_le (D2QE e ψ x' (inner ℝ x' e) - D2QE e ψ x (inner ℝ x' e))
    (D2QE e ψ x (inner ℝ x' e) - D2QE e ψ x (inner ℝ x e))
  linarith

end Hol3

section Ext6

variable {d : ℕ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

variable [IFacts d]

lemma cH_nonneg (hμ0 : 0 < μ) : 0 ≤ cH d μ := by
  have hA := wA_nonneg (d := d)
  have hgm := gm_pos d
  have h4 : 0 ≤ (4 : ℝ) ^ (μ / 2) := rpow_nonneg (by norm_num) _
  have h2μ : 0 ≤ (2 : ℝ) ^ μ := rpow_nonneg (by norm_num) _
  have hcT : 0 ≤ cTm d μ := by
    unfold cTm
    have : 0 ≤ (d : ℝ) / μ + 1 := by have := div_nonneg (Nat.cast_nonneg d) hμ0.le; linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg this hA) hgm.le) h4
  unfold cH
  have : 0 ≤ (2 + 2 ^ μ) * wA d * gm d * 4 ^ (μ / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hA) hgm.le) h4
  linarith

lemma cTK_nonneg : 0 ≤ cTK d μ := by
  have hA := wA_nonneg (d := d)
  have hgm := gm_pos d
  have h4 : 0 ≤ (4 : ℝ) ^ (μ / 2) := rpow_nonneg (by norm_num) _
  have h4' : 0 ≤ (4 : ℝ) ^ μ := rpow_nonneg (by norm_num) _
  have hL := norm_nonneg (lap2L d)
  unfold cTK
  have a1 := mul_nonneg (mul_nonneg hA hgm.le) h4
  have a2 := mul_nonneg (mul_nonneg (mul_nonneg hL hA) hgm.le) h4'
  linarith

/-- First derivative of the profile, extended to the plane by `ψ1`. -/
noncomputable def K1e (e : Eu d) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) (x : Eu d) :
    Eu d →L[ℝ] ℝ :=
  if inner ℝ x e = 0 then ψ1 x else kw1 univ wK1 ψ (inner ℝ x e ^ 2) x

lemma C1H.K1e_apply (hC : C1H d μ M0 M1 H ψ ψ1) (e x v : Eu d) :
    K1e e ψ ψ1 x v = FE e (fun y => ψ1 y v) x := by
  unfold K1e FE Wb
  by_cases h0 : inner ℝ x e = 0
  · rw [if_pos h0, h0]; simp
  · have hs : 0 < inner ℝ x e ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
    rw [if_neg h0, if_pos hs, kw1_trans hC.hd hC.cont hC.b0 hC.b1 hs x v]

lemma C1H.K1e_hol (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d}
    (he : ‖e‖ = 1) (x x' : Eu d) :
    ‖K1e e ψ ψ1 x - K1e e ψ ψ1 x'‖ ≤ cH d μ * H * ‖x - x'‖ ^ μ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (cH_nonneg hμ0) hC.hH) (rpow_nonneg (norm_nonneg _) _)) fun v => ?_
  rw [ContinuousLinearMap.sub_apply, hC.K1e_apply, hC.K1e_apply, Real.norm_eq_abs]
  have := FE_hol (hC.holV v) (hC.measV v) hμ0 hμ1 he x x'
  calc _ ≤ cH d μ * (H * ‖v‖) * ‖x - x'‖ ^ μ := this
    _ = cH d μ * H * ‖x - x'‖ ^ μ * ‖v‖ := by ring

/-- `⟪x,e⟫ * lap2 (kw2 ψ (⟪x,e⟫²) x)` written as a sum of `TK` terms (vanishes on the plane). -/
noncomputable def TKs (e : Eu d) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) (x : Eu d) : ℝ :=
  ∑ i : Fin d, TK e (fun y => ψ1 y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)

lemma C1H.TKs_eq (hC : C1H d μ M0 M1 H ψ ψ1) {e x : Eu d} (h0 : inner ℝ x e ≠ 0) :
    TKs e ψ1 x = inner ℝ x e * lap2 (kw2 univ wK2 ψ (inner ℝ x e ^ 2) x) := by
  have hs : 0 < inner ℝ x e ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
  rw [hC.lap2_kw2_eq hs x, Finset.mul_sum]
  unfold TKs TK
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma C1H.TKs_hol (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d}
    (he : ‖e‖ = 1) (x x' : Eu d) :
    |TKs e ψ1 x - TKs e ψ1 x'| ≤ d * (cTK d μ * H * ‖x - x'‖ ^ μ) := by
  unfold TKs
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hi : ∀ i : Fin d,
      |TK e (fun y => ψ1 y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) -
        TK e (fun y => ψ1 y (EuclideanSpace.single i 1)) x' (EuclideanSpace.single i 1)| ≤
        cTK d μ * H * ‖x - x'‖ ^ μ := by
    intro i
    have h1 := TK_hol (hC.holV (EuclideanSpace.single i 1)) (hC.measV (EuclideanSpace.single i 1))
      hμ0 hμ1 he x x'
    rw [EuclideanSpace.norm_single, norm_one, mul_one] at h1
    rw [← ContinuousLinearMap.sub_apply, ← Real.norm_eq_abs]
    refine ((ContinuousLinearMap.le_opNorm _ _)).trans ?_
    rw [EuclideanSpace.norm_single, norm_one, mul_one]
    exact h1
  refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Extended derivative of the profile. -/
noncomputable def DFEe (e : Eu d) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) (x : Eu d) :
    Eu d →L[ℝ] ℝ :=
  TKs e ψ1 x • innerSL ℝ e + K1e e ψ ψ1 x

lemma C1H.DFEe_eq (hC : C1H d μ M0 M1 H ψ ψ1) {e x : Eu d} (h0 : inner ℝ x e ≠ 0) :
    DFEe e ψ ψ1 x = DFE e ψ x := by
  unfold DFEe DFE K1e; rw [hC.TKs_eq h0, if_neg h0]

/-- Extended second derivative of the extension. -/
noncomputable def D2EXTe (e : Eu d) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) (x : Eu d) :
    Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  D2QE e ψ x (inner ℝ x e) + (innerSL ℝ e).smulRight ((K1e e ψ ψ1 x).comp (PeL e))
    + (DFEe e ψ ψ1 x).smulRight (innerSL ℝ e)

lemma C1H.D2EXTe_eq (hC : C1H d μ M0 M1 H ψ ψ1) {e x : Eu d} (h0 : inner ℝ x e ≠ 0) :
    D2EXTe e ψ ψ1 x = D2EXT e ψ x := by
  unfold D2EXTe D2EXT DQI
  rw [hC.DFEe_eq h0, PeL_add_inner]
  unfold K1e; rw [if_neg h0]

lemma norm_smulRight_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : Eu d →L[ℝ] ℝ) (f g : F) : ‖c.smulRight f - c.smulRight g‖ ≤ ‖c‖ * ‖f - g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    fun u => ?_
  have e1 : (c.smulRight f - c.smulRight g) u = c u • (f - g) := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply]
    exact (smul_sub _ _ _).symm
  rw [e1, norm_smul]
  calc ‖c u‖ * ‖f - g‖ ≤ ‖c‖ * ‖u‖ * ‖f - g‖ :=
        mul_le_mul_of_nonneg_right (c.le_opNorm u) (norm_nonneg _)
    _ = ‖c‖ * ‖f - g‖ * ‖u‖ := by ring

lemma norm_smulRight_sub_le' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : Eu d →L[ℝ] ℝ) (c : F) : ‖f.smulRight c - g.smulRight c‖ ≤ ‖f - g‖ * ‖c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    fun u => ?_
  have e1 : (f.smulRight c - g.smulRight c) u = (f - g) u • c := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.sub_apply]
    exact (sub_smul _ _ _).symm
  rw [e1, norm_smul]
  calc ‖(f - g) u‖ * ‖c‖ ≤ ‖f - g‖ * ‖u‖ * ‖c‖ :=
        mul_le_mul_of_nonneg_right ((f - g).le_opNorm u) (norm_nonneg _)
    _ = ‖f - g‖ * ‖c‖ * ‖u‖ := by ring

/-- **Hölder continuity of the extended second derivative** on the closed half-space. -/
theorem C1H.D2EXTe_hol (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ < 1) {e : Eu d}
    (he : ‖e‖ = 1) : ∃ C, 0 ≤ C ∧ ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ‖D2EXTe e ψ ψ1 x' - D2EXTe e ψ ψ1 x‖ ≤ C * ‖x' - x‖ ^ μ := by
  have hP := norm_nonneg (PeL e)
  have hcH := cH_nonneg (d := d) hμ0
  have hcTK := cTK_nonneg (d := d) (μ := μ)
  have hH := hC.hH
  have hiS : ‖innerSL ℝ e‖ = 1 := by rw [innerSL_apply_norm, he]
  have hQ0 : 0 ≤ cQp d μ H e + ‖PeL e‖ ^ 2 * KB d μ H / μ := by
    have h1 : 0 ≤ cQp d μ H e := by
      unfold cQp
      have hKB := hC.KB_nonneg
      have hK1 := KH1_nonneg (d := d) (μ := μ) hH
      exact mul_nonneg (sq_nonneg _) (add_nonneg (div_nonneg (by linarith) hμ0.le)
        (div_nonneg (mul_nonneg hP hK1) (by linarith)))
    have h2 : 0 ≤ ‖PeL e‖ ^ 2 * KB d μ H / μ :=
      div_nonneg (mul_nonneg (sq_nonneg _) hC.KB_nonneg) hμ0.le
    linarith
  refine ⟨(cQp d μ H e + ‖PeL e‖ ^ 2 * KB d μ H / μ) + cH d μ * H * ‖PeL e‖ +
    (d * (cTK d μ * H) + cH d μ * H), ?_, fun x x' hx hx' => ?_⟩
  · have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have := mul_nonneg (mul_nonneg hcH hH) hP
    have := mul_nonneg hd0 (mul_nonneg hcTK hH)
    have := mul_nonneg hcH hH
    linarith
  have hδμ : 0 ≤ ‖x' - x‖ ^ μ := rpow_nonneg (norm_nonneg _) _
  have hA := hC.D2QE_hol hμ0 hμ1 he hx hx'
  have hK := hC.K1e_hol hμ0 hμ1.le he x' x
  have hT := hC.TKs_hol hμ0 hμ1.le he x' x
  have e1 : D2EXTe e ψ ψ1 x' - D2EXTe e ψ ψ1 x =
      (D2QE e ψ x' (inner ℝ x' e) - D2QE e ψ x (inner ℝ x e)) +
      ((innerSL ℝ e).smulRight ((K1e e ψ ψ1 x').comp (PeL e)) -
        (innerSL ℝ e).smulRight ((K1e e ψ ψ1 x).comp (PeL e))) +
      ((DFEe e ψ ψ1 x').smulRight (innerSL ℝ e) - (DFEe e ψ ψ1 x).smulRight (innerSL ℝ e)) := by
    unfold D2EXTe; abel
  rw [e1]
  have hB : ‖(innerSL ℝ e).smulRight ((K1e e ψ ψ1 x').comp (PeL e)) -
      (innerSL ℝ e).smulRight ((K1e e ψ ψ1 x).comp (PeL e))‖ ≤
      cH d μ * H * ‖PeL e‖ * ‖x' - x‖ ^ μ := by
    refine (norm_smulRight_sub_le _ _ _).trans ?_
    rw [hiS, one_mul, ← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖K1e e ψ ψ1 x' - K1e e ψ ψ1 x‖ * ‖PeL e‖ ≤ cH d μ * H * ‖x' - x‖ ^ μ * ‖PeL e‖ :=
          mul_le_mul_of_nonneg_right hK hP
      _ = _ := by ring
  have hDF : ‖DFEe e ψ ψ1 x' - DFEe e ψ ψ1 x‖ ≤
      (d * (cTK d μ * H) + cH d μ * H) * ‖x' - x‖ ^ μ := by
    have e2 : DFEe e ψ ψ1 x' - DFEe e ψ ψ1 x =
        (TKs e ψ1 x' - TKs e ψ1 x) • innerSL ℝ e + (K1e e ψ ψ1 x' - K1e e ψ ψ1 x) := by
      have hs : TKs e ψ1 x' • innerSL ℝ e - TKs e ψ1 x • innerSL ℝ e =
          (TKs e ψ1 x' - TKs e ψ1 x) • innerSL ℝ e := (sub_smul _ _ _).symm
      unfold DFEe; rw [← hs]; abel
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, hiS, mul_one, Real.norm_eq_abs]
    have : (d * (cTK d μ * H) + cH d μ * H) * ‖x' - x‖ ^ μ =
        d * (cTK d μ * H * ‖x' - x‖ ^ μ) + cH d μ * H * ‖x' - x‖ ^ μ := by ring
    rw [this]; exact add_le_add hT hK
  have hC3 : ‖(DFEe e ψ ψ1 x').smulRight (innerSL ℝ e) - (DFEe e ψ ψ1 x).smulRight (innerSL ℝ e)‖
      ≤ (d * (cTK d μ * H) + cH d μ * H) * ‖x' - x‖ ^ μ := by
    refine (norm_smulRight_sub_le' _ _ _).trans ?_
    rw [hiS, mul_one]; exact hDF
  have hn1 := norm_add_le ((D2QE e ψ x' (inner ℝ x' e) - D2QE e ψ x (inner ℝ x e)) +
      ((innerSL ℝ e).smulRight ((K1e e ψ ψ1 x').comp (PeL e)) -
        (innerSL ℝ e).smulRight ((K1e e ψ ψ1 x).comp (PeL e))))
      ((DFEe e ψ ψ1 x').smulRight (innerSL ℝ e) - (DFEe e ψ ψ1 x).smulRight (innerSL ℝ e))
  have hn2 := norm_add_le (D2QE e ψ x' (inner ℝ x' e) - D2QE e ψ x (inner ℝ x e))
      ((innerSL ℝ e).smulRight ((K1e e ψ ψ1 x').comp (PeL e)) -
        (innerSL ℝ e).smulRight ((K1e e ψ ψ1 x).comp (PeL e)))
  linarith

end Ext6

section Pkg

variable {d : ℕ}

variable [IFacts d]

/-- For every bounded `C^{1,μ}` function `ψ` on `ℝ^d` and unit `e`, there is a `C¹` function `E` vanishing on the
plane `⟪x,e⟫ = 0` with normal derivative `ψ` there (`DE x = ψ x • ⟪·,e⟫`), `C²` on the open half-space, whose second
derivative extends `μ`-Hölder continuously to the closed half-space. -/
def ExtPackage (d : ℕ) (μ : ℝ) : Prop :=
  ∀ (M0 M1 H : ℝ) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) (e : Eu d),
    (∀ y, HasFDerivAt ψ (ψ1 y) y) → Continuous ψ1 → (∀ y, |ψ y| ≤ M0) → (∀ y, ‖ψ1 y‖ ≤ M1) →
    (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) → 0 ≤ H → ‖e‖ = 1 →
    ∃ (E : Eu d → ℝ) (DE : Eu d → (Eu d →L[ℝ] ℝ)) (D2E : Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)),
      (∀ x, HasStrictFDerivAt E (DE x) x) ∧ Continuous DE ∧
      (∀ x, inner ℝ x e = 0 → E x = 0 ∧ DE x = ψ x • innerSL ℝ e) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DE (D2E x) x) ∧
      ∃ C, 0 ≤ C ∧ ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
        ‖D2E x' - D2E x‖ ≤ C * ‖x' - x‖ ^ μ

theorem extPackage {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) : ExtPackage d μ := by
  intro M0 M1 H ψ ψ1 e hd hc hb0 hb1 hhol hH he
  have hC : C1H d μ M0 M1 H ψ ψ1 := ⟨hd, hc, hb0, hb1, hhol, hH⟩
  refine ⟨EXT e ψ, DEXT e ψ, D2EXTe e ψ ψ1, fun x => hC.EXT_strict he x, hC.DEXT_continuous he,
    fun x hx => ⟨EXT_plane hx, DEXT_plane hx⟩, fun x hx => ?_, hC.D2EXTe_hol hμ0 hμ1 he⟩
  rw [hC.D2EXTe_eq hx.ne']
  exact hC.DEXT_hasFDerivAt hμ0 hμ1.le hx

end Pkg

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
    ∀ (μ : ℝ), 0 < μ → μ < 1 →
  ∀ (M0 M1 H : ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (e : EuclideanSpace ℝ (Fin d)),
      (∀ y, HasFDerivAt ψ (ψ1 y) y) → Continuous ψ1 → (∀ y, |ψ y| ≤ M0) → (∀ y, ‖ψ1 y‖ ≤ M1) →
      (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) → 0 ≤ H → ‖e‖ = 1 →
      ∃ (E : EuclideanSpace ℝ (Fin d) → ℝ) (DE : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (D2E : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)),
        (∀ x, HasStrictFDerivAt E (DE x) x) ∧ Continuous DE ∧
        (∀ x, inner ℝ x e = 0 → E x = 0 ∧ DE x = ψ x • innerSL ℝ e) ∧
        (∀ x, 0 < inner ℝ x e → HasFDerivAt DE (D2E x) x) ∧
        ∃ C, 0 ≤ C ∧ ∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
          ‖D2E x' - D2E x‖ ≤ C * ‖x' - x‖ ^ μ := by
  intro d
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_kw1_trans, f_kw2_trans, f_kw3_trans, f_wh_hasDerivAt_kw0_t, f_wh_hasFDerivAt_kw0, f_wh_hasFDerivAt_kw1, f_wh_hasFDerivAt_kw2, f_wh_kw0_le, f_wh_kw0_sub_h, f_wh_kw0_time_diff, f_wh_kw1_hol, f_wh_kw1_le, f_wh_kw1_time_le, f_wh_kw2_hol, f_wh_kw1_lip⟩ := @EthierKurtz.heat_kernel_smoothing_estimates d
  obtain ⟨f_C1H_continuous, f_C1H_holV, f_C1H_measV, f_C1H_lap2_kw2_eq, f_PeL_add_inner, f_C1H_EXT_strict, f_C1H_DEXT_continuous, f_EXT_plane, f_DEXT_plane, f_C1H_KB_nonneg, f_norm_flipP_le, f_C1H_D2QI_le, f_C1H_D2QI_ii, f_C1H_DEXT_hasFDerivAt⟩ := @EthierKurtz.heat_extension_c1mu_properties d
  obtain ⟨f_FE_hol, f_KH1_nonneg, f_kw2h_tau_le, f_TK_hol⟩ := @EthierKurtz.heat_extension_holder_estimates d
  haveI : ObliqueLib.IFacts d := ⟨f_wA_nonneg, f_kw1_trans, f_kw3_trans, f_wh_hasFDerivAt_kw2, f_C1H_continuous, f_C1H_holV, f_C1H_measV, f_C1H_lap2_kw2_eq, f_PeL_add_inner, f_C1H_EXT_strict, f_C1H_DEXT_continuous, f_EXT_plane, f_DEXT_plane, f_C1H_KB_nonneg, f_norm_flipP_le, f_C1H_D2QI_le, f_C1H_D2QI_ii, f_C1H_DEXT_hasFDerivAt, f_FE_hol, f_KH1_nonneg, f_kw2h_tau_le, f_TK_hol⟩
  intro μ hμ0 hμ1
  exact ObliqueLib.extPackage hμ0 hμ1
