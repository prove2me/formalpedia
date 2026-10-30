-- Prove2me | solution 1 for EthierKurtz.heat_extension_c1mu_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T14:33:07.315845+00:00
-- url     : https://prove2.me/submissions/163c021c-b481-4511-9568-c8f3eea82e73

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_heat_kernel_smoothing_estimates

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

theorem C1H.hol (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ := hC.2.2.2.2.1

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

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  wA_nonneg : 0 ≤ wA d
  kw1_trans : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x v : Eu d), kw1 univ wK1 ψ t x v = kw0 univ (wK d) (fun y => ψ1 y v) t x
  kw2_trans : ∀ {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x u v : Eu d), kw2 univ wK2 ψ t x u v = kw1 univ wK1 (fun y => ψ1 y v) t x u
  wh_hasDerivAt_kw0_t : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), HasDerivAt (fun t => kw0 univ (wK d) h t x) ((1 / 2 : ℝ) * lap2 (kw2 univ wK2 h t x)) t
  wh_hasFDerivAt_kw0 : ∀ {h : Eu d → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (Eu d)), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw0 univ (wK d) h t) (kw1 univ wK1 h t x) x
  wh_hasFDerivAt_kw1 : ∀ {h : Eu d → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (Eu d)), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw1 univ wK1 h t) (kw2 univ wK2 h t x) x
  wh_kw0_le : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), |kw0 univ (wK d) h t x| ≤ wA d * M0
  wh_kw0_sub_h : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), |kw0 univ (wK d) h t x - h x| ≤ wA d * Hh * (gm d * (4 * t) ^ (μ / 2))
  wh_kw0_time_diff : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), kw0 univ (wK d) h s' x - kw0 univ (wK d) h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 univ wK2 h σ x)
  wh_kw1_hol : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), ‖kw1 univ wK1 h t x‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * Hh * (gm d * (4 * t) ^ (μ / 2))
  wh_kw1_le : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), ‖kw1 univ wK1 h t x‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * M0
  wh_kw1_time_le : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ (univ : Set (Eu d))), ‖kw1 univ wK1 h s' x - kw1 univ wK1 h s x‖ ≤ (1 / 2 : ℝ) * (‖lap2L d‖ * (wA d * s ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (4 * s') ^ (μ / 2)))) * (s' - s)
  wh_kw1_lip : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x x' : Eu d} (hx : x ∈ (univ : Set (Eu d))) (hx' : x' ∈ (univ : Set (Eu d))), ‖kw1 univ wK1 h t x - kw1 univ wK1 h t x'‖ ≤ wA d * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖

end IFk

export IFacts (wA_nonneg kw1_trans kw2_trans wh_hasDerivAt_kw0_t wh_hasFDerivAt_kw0 wh_hasFDerivAt_kw1 wh_kw0_le wh_kw0_sub_h wh_kw0_time_diff wh_kw1_hol wh_kw1_le wh_kw1_time_le wh_kw1_lip)

section Ext1

variable {d : ℕ}

variable [IFacts d]

/-- Heat extension with value `h` at time `0`. -/
noncomputable def Wb (h : Eu d → ℝ) (s : ℝ) (x : Eu d) : ℝ :=
  if 0 < s then kw0 univ (wK d) h s x else h x

/-- Boundary profile: `FE e ψ y = Wb ψ (⟪y,e⟫²) y`. -/
noncomputable def FE (e : Eu d) (ψ : Eu d → ℝ) (y : Eu d) : ℝ := Wb ψ (inner ℝ y e ^ 2) y

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

lemma C1H.M0_nonneg (hC : C1H d μ M0 M1 H ψ ψ1) : 0 ≤ M0 := (abs_nonneg _).trans (hC.b0 0)

lemma C1H.M1_nonneg (hC : C1H d μ M0 M1 H ψ ψ1) : 0 ≤ M1 := (norm_nonneg _).trans (hC.b1 0)

lemma C1H.continuous (hC : C1H d μ M0 M1 H ψ ψ1) : Continuous ψ :=
  continuous_iff_continuousAt.mpr fun y => (hC.hd y).continuousAt

lemma C1H.lip (hC : C1H d μ M0 M1 H ψ ψ1) (y z : Eu d) : |ψ y - ψ z| ≤ M1 * ‖y - z‖ := by
  rw [← Real.norm_eq_abs]
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hC.hd x).hasFDerivWithinAt) (fun x _ => hC.b1 x) convex_univ trivial trivial

lemma C1H.holS (hC : C1H d μ M0 M1 H ψ ψ1) : HolderOnS univ 1 M0 M1 ψ :=
  ⟨hC.M0_nonneg, hC.M1_nonneg, fun y _ => hC.b0 y, fun y _ z _ => by
    rw [rpow_one]; exact hC.lip y z⟩

lemma C1H.holV (hC : C1H d μ M0 M1 H ψ ψ1) (v : Eu d) :
    HolderOnS univ μ (M1 * ‖v‖) (H * ‖v‖) (fun y => ψ1 y v) := by
  refine ⟨mul_nonneg hC.M1_nonneg (norm_nonneg _), mul_nonneg hC.hH (norm_nonneg _),
    fun y _ => ?_, fun y _ z _ => ?_⟩
  · rw [← Real.norm_eq_abs]
    exact ((ψ1 y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hC.b1 y) (norm_nonneg v))
  · rw [← Real.norm_eq_abs, ← ContinuousLinearMap.sub_apply]
    refine ((ψ1 y - ψ1 z).le_opNorm v).trans ?_
    have := mul_le_mul_of_nonneg_right (hC.hol y z) (norm_nonneg v)
    linarith [this, show H * ‖y - z‖ ^ μ * ‖v‖ = H * ‖v‖ * ‖y - z‖ ^ μ by ring]

lemma C1H.measV (hC : C1H d μ M0 M1 H ψ ψ1) (v : Eu d) :
    AEStronglyMeasurable (fun y => ψ1 y v) (volume.restrict (univ : Set (Eu d))) :=
  ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hC.cont).aestronglyMeasurable

lemma one_le_wA : 1 ≤ wA d := by
  unfold wA
  have : (1 : ℝ) ≤ 2 ^ ((d : ℝ) / 2) := one_le_rpow (by norm_num) (by positivity)
  linarith

/-- `‖kw1 ψ‖ ≤ wA d * M1` (transfer). -/
lemma C1H.kw1_norm_le (hC : C1H d μ M0 M1 H ψ ψ1) {s : ℝ} (hs : 0 < s) (y : Eu d) :
    ‖kw1 univ wK1 ψ s y‖ ≤ wA d * M1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg wA_nonneg hC.M1_nonneg) fun v => ?_
  rw [kw1_trans hC.hd hC.cont hC.b0 hC.b1 hs y v, Real.norm_eq_abs]
  have := wh_kw0_le (hC.holV v) (hC.measV v) hs (mem_univ y)
  linarith [this, show wA d * (M1 * ‖v‖) = wA d * M1 * ‖v‖ by ring]

/-- `|lap2 (kw2 ψ σ y)| ≤ d * wA d * σ^(-1/2) * M1` (transfer). -/
lemma C1H.lap2_kw2_le (hC : C1H d μ M0 M1 H ψ ψ1) {σ : ℝ} (hσ : 0 < σ) (y : Eu d) :
    |lap2 (kw2 univ wK2 ψ σ y)| ≤ d * (wA d * σ ^ (-(1 / 2 : ℝ)) * M1) := by
  unfold lap2
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin d, |kw2 univ wK2 ψ σ y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)|
      ≤ wA d * σ ^ (-(1 / 2 : ℝ)) * M1 := fun i => by
    rw [kw2_trans hC.hd hC.cont hC.b0 hC.b1 hσ, ← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [EuclideanSpace.norm_single, norm_one, mul_one]
    have := wh_kw1_le (hC.holV (EuclideanSpace.single i 1))
      (hC.measV (EuclideanSpace.single i 1)) hσ (mem_univ y)
    rwa [EuclideanSpace.norm_single, norm_one, mul_one] at this
  refine (Finset.sum_le_sum fun i _ => this i).trans ?_
  simp

/-- Space Lipschitz bound of `Wb ψ s`. -/
lemma C1H.Wb_space (hC : C1H d μ M0 M1 H ψ ψ1) {s : ℝ} (y y' : Eu d) :
    |Wb ψ s y' - Wb ψ s y| ≤ wA d * M1 * ‖y' - y‖ := by
  unfold Wb
  split_ifs with hs
  · rw [← Real.norm_eq_abs]
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (wh_hasFDerivAt_kw0 hC.continuous.aestronglyMeasurable
        (fun y _ => hC.b0 y) hs z).hasFDerivWithinAt) (fun z _ => hC.kw1_norm_le hs z)
      convex_univ trivial trivial
  · refine (hC.lip y' y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact le_mul_of_one_le_left hC.M1_nonneg one_le_wA

/-- Constant of the `√s` time bound. -/
noncomputable def wT (d : ℕ) : ℝ := d * wA d + 4 * wA d * gm d

lemma wT_nonneg : 0 ≤ wT d := by
  unfold wT; have := wA_nonneg (d := d); have := gm_pos d; positivity

/-- Time bound: `|Wb ψ s' y - Wb ψ s y| ≤ wT d * M1 * (s'^(1/2) - s^(1/2))` for `0 ≤ s ≤ s'`. -/
lemma C1H.Wb_time (hC : C1H d μ M0 M1 H ψ ψ1) {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') (y : Eu d) :
    |Wb ψ s' y - Wb ψ s y| ≤ wT d * M1 * (s' ^ (1 / 2 : ℝ) - s ^ (1 / 2 : ℝ)) := by
  have hM1 := hC.M1_nonneg
  have hA := wA_nonneg (d := d)
  have hgm := gm_pos d
  rcases hs.lt_or_eq with hs0 | hs0
  · have hs' : 0 < s' := lt_of_lt_of_le hs0 hss
    unfold Wb
    rw [if_pos hs', if_pos hs0, wh_kw0_time_diff hC.holS
      hC.continuous.aestronglyMeasurable hs0 hss (mem_univ y), ← Real.norm_eq_abs]
    have hI : IntervalIntegrable (fun σ : ℝ => (1 / 2 : ℝ) * (d * (wA d * M1)) * σ ^ (-(1 / 2 : ℝ)))
        volume s s' :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
    refine (intervalIntegral.norm_integral_le_of_norm_le hss (Eventually.of_forall fun σ hσ => ?_)
      hI).trans ?_
    · have hσ0 : 0 < σ := lt_trans hs0 hσ.1
      have := hC.lap2_kw2_le hσ0 y
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith [this]
    · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      have e : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
      rw [e]
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hsq : s ^ (1 / 2 : ℝ) ≤ s' ^ (1 / 2 : ℝ) := rpow_le_rpow hs hss (by norm_num)
      unfold wT
      have : (1 / 2 : ℝ) * (d * (wA d * M1)) * ((s' ^ (1 / 2 : ℝ) - s ^ (1 / 2 : ℝ)) / (1 / 2))
          = d * wA d * M1 * (s' ^ (1 / 2 : ℝ) - s ^ (1 / 2 : ℝ)) := by field_simp
      rw [this]
      have h4 : 0 ≤ 4 * wA d * gm d * M1 * (s' ^ (1 / 2 : ℝ) - s ^ (1 / 2 : ℝ)) := by
        have := sub_nonneg.mpr hsq; positivity
      linarith [h4]
  · subst hs0
    rw [zero_rpow (by norm_num), sub_zero]
    rcases hss.lt_or_eq with hs' | hs'
    · unfold Wb
      rw [if_pos hs', if_neg (lt_irrefl 0)]
      have := wh_kw0_sub_h hC.holS hC.continuous.aestronglyMeasurable (by norm_num)
        (by norm_num) hs' (mem_univ y)
      have e : ((4 : ℝ) * s') ^ ((1 : ℝ) / 2) = 2 * s' ^ (1 / 2 : ℝ) := by
        rw [mul_rpow (by norm_num) hs'.le]
        congr 1
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← rpow_mul (by norm_num)]; norm_num
      rw [e] at this
      refine this.trans ?_
      unfold wT
      have hp : 0 ≤ s' ^ (1 / 2 : ℝ) := rpow_nonneg hs'.le _
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have h5 : 0 ≤ d * wA d * M1 * s' ^ (1 / 2 : ℝ) := by positivity
      have h6 : 0 ≤ wA d * gm d * M1 * s' ^ (1 / 2 : ℝ) := by positivity
      have e2 : wA d * M1 * (gm d * (2 * s' ^ (1 / 2 : ℝ))) = 2 * (wA d * gm d * M1 * s' ^ (1 / 2 : ℝ)) := by ring
      have e3 : (d * wA d + 4 * wA d * gm d) * M1 * s' ^ (1 / 2 : ℝ) =
        d * wA d * M1 * s' ^ (1 / 2 : ℝ) + 4 * (wA d * gm d * M1 * s' ^ (1 / 2 : ℝ)) := by ring
      rw [e2, e3]; linarith
    · subst hs'
      simp only [sub_self, abs_zero, zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero, le_refl]

lemma C1H.Wb_time' (hC : C1H d μ M0 M1 H ψ ψ1) {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') (y : Eu d) :
    |Wb ψ s' y - Wb ψ s y| ≤ wT d * M1 * |s' ^ (1 / 2 : ℝ) - s ^ (1 / 2 : ℝ)| := by
  rcases le_total s s' with h | h
  · have := hC.Wb_time hs h y
    rwa [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hs h (by norm_num)))]
  · have := hC.Wb_time hs' h y
    rw [abs_sub_comm, abs_sub_comm (s' ^ _)]
    rwa [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hs' h (by norm_num)))]

lemma sq_rpow_half (t : ℝ) : (t ^ 2) ^ (1 / 2 : ℝ) = |t| := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

/-- The boundary profile is Lipschitz. -/
lemma C1H.FE_lip (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1) (y y' : Eu d) :
    |FE e ψ y' - FE e ψ y| ≤ (wA d + wT d) * M1 * ‖y' - y‖ := by
  unfold FE
  have h1 := hC.Wb_space (s := inner ℝ y' e ^ 2) y y'
  have h2 := hC.Wb_time' (sq_nonneg (inner ℝ y e)) (sq_nonneg (inner ℝ y' e)) y
  rw [sq_rpow_half, sq_rpow_half] at h2
  have h3 : |(|inner ℝ y' e| - |inner ℝ y e|)| ≤ ‖y' - y‖ := by
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [← inner_sub_left]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [he, mul_one]
  have hT := wT_nonneg (d := d)
  have hM1 := hC.M1_nonneg
  calc |Wb ψ (inner ℝ y' e ^ 2) y' - Wb ψ (inner ℝ y e ^ 2) y|
      ≤ |Wb ψ (inner ℝ y' e ^ 2) y' - Wb ψ (inner ℝ y' e ^ 2) y|
        + |Wb ψ (inner ℝ y' e ^ 2) y - Wb ψ (inner ℝ y e ^ 2) y| := abs_sub_le _ _ _
    _ ≤ wA d * M1 * ‖y' - y‖ + wT d * M1 * ‖y' - y‖ := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left h3 (mul_nonneg hT hM1))
    _ = (wA d + wT d) * M1 * ‖y' - y‖ := by ring

lemma FE_plane {e : Eu d} {y : Eu d} (hy : inner ℝ y e = 0) : FE e ψ y = ψ y := by
  unfold FE Wb; rw [hy]; simp

end Ext1

section Ext2

variable {d : ℕ}

variable [IFacts d]

/-- Joint continuity of `(s, y) ↦ kw1 univ wK1 h s y` at `s₀ > 0`. -/
lemma kw1_contAt {h : Eu d → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (y₀ : Eu d) :
    ContinuousAt (fun p : ℝ × Eu d => kw1 univ wK1 h p.1 p.2) (s₀, y₀) := by
  have hA := wA_nonneg (d := d)
  have hM : 0 ≤ M := hhol.1
  have hHh : 0 ≤ Hh := hhol.2.1
  have hgm := gm_pos d
  set C1 : ℝ := wA d * (s₀ / 2) ^ (-(1 : ℝ)) * M with hC1
  set C2 : ℝ := (1 / 2 : ℝ) * (‖lap2L d‖ * (wA d * (s₀ / 2) ^ (-(3 / 2 : ℝ)) * Hh *
    (gm d * (4 * (2 * s₀)) ^ (μ / 2)))) with hC2
  have hC2n : 0 ≤ C2 := by
    have : 0 ≤ (s₀ / 2) ^ (-(3 / 2 : ℝ)) := rpow_nonneg (by linarith) _
    have : 0 ≤ (4 * (2 * s₀)) ^ (μ / 2) := rpow_nonneg (by linarith) _
    positivity
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hev : ∀ᶠ p : ℝ × Eu d in 𝓝 (s₀, y₀), s₀ / 2 < p.1 ∧ p.1 < 2 * s₀ :=
    (continuous_fst.tendsto (s₀, y₀)).eventually
      (Ioo_mem_nhds (by linarith : s₀ / 2 < s₀) (by linarith : s₀ < 2 * s₀))
  refine squeeze_zero' (Eventually.of_forall fun p => norm_nonneg _) ?_
    (g := fun p : ℝ × Eu d => C1 * ‖p.2 - y₀‖ + C2 * |p.1 - s₀|) ?_
  · filter_upwards [hev] with p hp
    have hp0 : 0 < p.1 := by linarith [hp.1]
    have hinv : p.1 ^ (-(1 : ℝ)) ≤ (s₀ / 2) ^ (-(1 : ℝ)) :=
      rpow_le_rpow_of_nonpos (by linarith) hp.1.le (by norm_num)
    have e1 : ‖kw1 univ wK1 h p.1 p.2 - kw1 univ wK1 h p.1 y₀‖ ≤ C1 * ‖p.2 - y₀‖ := by
      refine (wh_kw1_lip hhol hh hp0 (mem_univ _) (mem_univ _)).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv hA) hM) (norm_nonneg _)
    have e2 : ‖kw1 univ wK1 h p.1 y₀ - kw1 univ wK1 h s₀ y₀‖ ≤ C2 * |p.1 - s₀| := by
      rcases le_total s₀ p.1 with hle | hle
      · refine (wh_kw1_time_le hhol hh hμ0 hμ2 hs₀ hle one_pos (subset_univ _)).trans ?_
        rw [abs_of_nonneg (by linarith)]
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h3 : s₀ ^ (-(3 / 2 : ℝ)) ≤ (s₀ / 2) ^ (-(3 / 2 : ℝ)) :=
          rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
        have h4 : (4 * p.1) ^ (μ / 2) ≤ (4 * (2 * s₀)) ^ (μ / 2) :=
          rpow_le_rpow (by linarith) (by linarith [hp.2]) (by linarith)
        have : 0 ≤ (4 * p.1) ^ (μ / 2) := rpow_nonneg (by linarith) _
        gcongr
      · rw [norm_sub_rev]
        refine (wh_kw1_time_le hhol hh hμ0 hμ2 hp0 hle one_pos (subset_univ _)).trans ?_
        rw [abs_of_nonpos (by linarith), neg_sub]
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h3 : p.1 ^ (-(3 / 2 : ℝ)) ≤ (s₀ / 2) ^ (-(3 / 2 : ℝ)) :=
          rpow_le_rpow_of_nonpos (by linarith) hp.1.le (by norm_num)
        have h4 : (4 * s₀) ^ (μ / 2) ≤ (4 * (2 * s₀)) ^ (μ / 2) :=
          rpow_le_rpow (by linarith) (by linarith) (by linarith)
        have : 0 ≤ (4 * s₀) ^ (μ / 2) := rpow_nonneg (by linarith) _
        have : 0 ≤ p.1 ^ (-(3 / 2 : ℝ)) := rpow_nonneg hp0.le _
        gcongr
    calc ‖kw1 univ wK1 h p.1 p.2 - kw1 univ wK1 h s₀ y₀‖
        ≤ ‖kw1 univ wK1 h p.1 p.2 - kw1 univ wK1 h p.1 y₀‖
          + ‖kw1 univ wK1 h p.1 y₀ - kw1 univ wK1 h s₀ y₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C1 * ‖p.2 - y₀‖ + C2 * |p.1 - s₀| := add_le_add e1 e2
  · have hc : Continuous fun p : ℝ × Eu d => C1 * ‖p.2 - y₀‖ + C2 * |p.1 - s₀| := by fun_prop
    have := hc.tendsto (s₀, y₀)
    simpa using this

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

/-- `lap2 (kw2 ψ)` via the transfer, as a sum of `kw1 (ψ1 e_i) e_i`. -/
lemma C1H.lap2_kw2_eq (hC : C1H d μ M0 M1 H ψ ψ1) {s : ℝ} (hs : 0 < s) (y : Eu d) :
    lap2 (kw2 univ wK2 ψ s y) = ∑ i : Fin d,
      kw1 univ wK1 (fun z => ψ1 z (EuclideanSpace.single i 1)) s y (EuclideanSpace.single i 1) := by
  unfold lap2
  exact Finset.sum_congr rfl fun i _ => kw2_trans hC.hd hC.cont hC.b0 hC.b1 hs y _ _

lemma C1H.lap2_contAt (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (y₀ : Eu d) :
    ContinuousAt (fun p : ℝ × Eu d => lap2 (kw2 univ wK2 ψ p.1 p.2)) (s₀, y₀) := by
  have hev : ∀ᶠ p : ℝ × Eu d in 𝓝 (s₀, y₀), 0 < p.1 :=
    (continuous_fst.tendsto (s₀, y₀)).eventually (Ioi_mem_nhds hs₀)
  have hc : ContinuousAt (fun p : ℝ × Eu d => ∑ i : Fin d,
      kw1 univ wK1 (fun z => ψ1 z (EuclideanSpace.single i 1)) p.1 p.2
        (EuclideanSpace.single i 1)) (s₀, y₀) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    exact ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).continuous.continuousAt).comp
      (kw1_contAt (hC.holV _) (hC.measV _) hμ0 hμ2 hs₀ y₀)
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact hC.lap2_kw2_eq hp p.2

lemma C1H.W_df1 (hC : C1H d μ M0 M1 H ψ ψ1) {s₀ : ℝ} (hs₀ : 0 < s₀) (y₀ : Eu d) :
    ∀ᶠ v : ℝ × Eu d in 𝓝 (s₀, y₀), HasFDerivAt (fun s => kw0 univ (wK d) ψ s v.2)
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((1 / 2 : ℝ) * lap2 (kw2 univ wK2 ψ v.1 v.2))) v.1 := by
  have hev : ∀ᶠ p : ℝ × Eu d in 𝓝 (s₀, y₀), 0 < p.1 :=
    (continuous_fst.tendsto (s₀, y₀)).eventually (Ioi_mem_nhds hs₀)
  filter_upwards [hev] with p hp
  exact (wh_hasDerivAt_kw0_t hC.holS hC.continuous.aestronglyMeasurable hp
    (mem_univ p.2)).hasFDerivAt

lemma C1H.W_df2 (hC : C1H d μ M0 M1 H ψ ψ1) {s₀ : ℝ} (hs₀ : 0 < s₀) (y₀ : Eu d) :
    ∀ᶠ v : ℝ × Eu d in 𝓝 (s₀, y₀), HasFDerivAt (fun y => kw0 univ (wK d) ψ v.1 y)
      (kw1 univ wK1 ψ v.1 v.2) v.2 := by
  have hev : ∀ᶠ p : ℝ × Eu d in 𝓝 (s₀, y₀), 0 < p.1 :=
    (continuous_fst.tendsto (s₀, y₀)).eventually (Ioi_mem_nhds hs₀)
  filter_upwards [hev] with p hp
  exact wh_hasFDerivAt_kw0 hC.continuous.aestronglyMeasurable (fun y _ => hC.b0 y) hp p.2

lemma smulRight_one_cont : Continuous fun a : ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight ((1 / 2 : ℝ) * a) := by
  have e : (fun a : ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight ((1 / 2 : ℝ) * a)) =
      fun a => ((1 / 2 : ℝ) * a) • (1 : ℝ →L[ℝ] ℝ) := by
    funext a; ext; simp
  rw [e]; exact (continuous_const.mul continuous_id).smul continuous_const

lemma C1H.W_cf1 (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (y₀ : Eu d) : ContinuousAt (fun v : ℝ × Eu d =>
      (1 : ℝ →L[ℝ] ℝ).smulRight ((1 / 2 : ℝ) * lap2 (kw2 univ wK2 ψ v.1 v.2))) (s₀, y₀) :=
  smulRight_one_cont.continuousAt.comp (hC.lap2_contAt hμ0 hμ2 hs₀ y₀)

lemma C1H.W_cf2 (hC : C1H d μ M0 M1 H ψ ψ1) {s₀ : ℝ} (hs₀ : 0 < s₀) (y₀ : Eu d) :
    ContinuousAt (fun v : ℝ × Eu d => kw1 univ wK1 ψ v.1 v.2) (s₀, y₀) :=
  kw1_contAt hC.holS hC.continuous.aestronglyMeasurable (by norm_num) (by norm_num) hs₀ y₀

/-- Strict joint derivative of the heat extension at `s₀ > 0`. -/
lemma C1H.W_strict (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (y₀ : Eu d) :
    HasStrictFDerivAt (Function.uncurry fun s y => kw0 univ (wK d) ψ s y)
      (((1 : ℝ →L[ℝ] ℝ).smulRight ((1 / 2 : ℝ) * lap2 (kw2 univ wK2 ψ s₀ y₀))).coprod
        (kw1 univ wK1 ψ s₀ y₀)) (s₀, y₀) :=
  hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (s₀, y₀))
    (f := fun s y => kw0 univ (wK d) ψ s y)
    (f₁ := fun s y => (1 : ℝ →L[ℝ] ℝ).smulRight ((1 / 2 : ℝ) * lap2 (kw2 univ wK2 ψ s y)))
    (f₂ := fun s y => kw1 univ wK1 ψ s y) (hC.W_df1 hs₀ y₀) (hC.W_df2 hs₀ y₀)
    (hC.W_cf1 hμ0 hμ2 hs₀ y₀) (hC.W_cf2 hs₀ y₀)

/-- Derivative of the profile off the plane. -/
noncomputable def DFE (e : Eu d) (ψ : Eu d → ℝ) (y : Eu d) : Eu d →L[ℝ] ℝ :=
  (inner ℝ y e * lap2 (kw2 univ wK2 ψ (inner ℝ y e ^ 2) y)) • innerSL ℝ e
    + kw1 univ wK1 ψ (inner ℝ y e ^ 2) y

lemma C1H.hasFDerivAt_FE (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {e y : Eu d}
    (hy : inner ℝ y e ≠ 0) : HasFDerivAt (FE e ψ) (DFE e ψ y) y := by
  have hs : 0 < inner ℝ y e ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hy))
  have h1 : HasFDerivAt (fun y' : Eu d => inner ℝ y' e) (innerSL ℝ e) y :=
    ((innerSL ℝ e).hasFDerivAt).congr_of_eventuallyEq
      (Eventually.of_forall fun y' => by simp [real_inner_comm])
  have h2 : HasFDerivAt (fun y' : Eu d => inner ℝ y' e ^ 2)
      ((2 * inner ℝ y e) • innerSL ℝ e) y := by
    refine (h1.pow 2).congr_fderiv ?_
    ext v; simp
  have hm : HasFDerivAt (fun y' : Eu d => (inner ℝ y' e ^ 2, y'))
      (((2 * inner ℝ y e) • innerSL ℝ e).prod (ContinuousLinearMap.id ℝ (Eu d))) y :=
    h2.prodMk (hasFDerivAt_id y)
  have hW := HasFDerivAt.comp (f := fun y' : Eu d => (inner ℝ y' e ^ 2, y')) y
    (hC.W_strict hμ0 hμ2 hs y).hasFDerivAt hm
  have hev : ∀ᶠ y' in 𝓝 y, 0 < inner ℝ y' e ^ 2 := by
    have hc : Continuous fun y' : Eu d => inner ℝ y' e ^ 2 := by fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds hs)
  have hcongr : FE e ψ =ᶠ[𝓝 y] ((Function.uncurry fun s y => kw0 univ (wK d) ψ s y) ∘
      (fun y' : Eu d => (inner ℝ y' e ^ 2, y'))) := by
    filter_upwards [hev] with y' hy'
    simp only [FE, Wb, Function.comp, Function.uncurry_apply_pair, if_pos hy']
  refine (hW.congr_of_eventuallyEq hcongr).congr_fderiv ?_
  ext v
  simp only [DFE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
  ring

end Ext2

section Ext3

variable {d : ℕ}

variable [IFacts d]

/-- Orthogonal projection onto `e⊥` (for a unit vector `e`), as a CLM. -/
noncomputable def PeL (e : Eu d) : Eu d →L[ℝ] Eu d :=
  ContinuousLinearMap.id ℝ (Eu d) - (innerSL ℝ e).smulRight e

lemma PeL_apply (e x : Eu d) : PeL e x = x - inner ℝ x e • e := by
  simp [PeL, real_inner_comm]

lemma inner_PeL_add {e : Eu d} (he : ‖e‖ = 1) (p : Eu d) (τ : ℝ) :
    inner ℝ (PeL e p + τ • e) e = τ := by
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  rw [PeL_apply, inner_add_left, inner_sub_left, inner_smul_left, inner_smul_left, hee]
  simp

/-- `Q e ψ p b = ∫_0^b FE e ψ (P p + τ e) dτ`. -/
noncomputable def QE (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (b : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..b, FE e ψ (PeL e p + τ • e)

/-- The extension. -/
noncomputable def EXT (e : Eu d) (ψ : Eu d → ℝ) (x : Eu d) : ℝ := QE e ψ x (inner ℝ x e)

/-- `p`-derivative of `QE`. -/
noncomputable def DQE (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (b : ℝ) : Eu d →L[ℝ] ℝ :=
  ∫ τ in (0 : ℝ)..b, (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

lemma C1H.FE_continuous (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1) :
    Continuous (FE e ψ) := by
  have hK : 0 ≤ (wA d + wT d) * M1 :=
    mul_nonneg (add_nonneg wA_nonneg wT_nonneg) hC.M1_nonneg
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal ((wA d + wT d) * M1))
    fun y y' => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK]
  exact hC.FE_lip he y' y

lemma C1H.QE_hasStrictDerivAt_b (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1)
    (p : Eu d) (b : ℝ) :
    HasStrictDerivAt (fun b => QE e ψ p b) (FE e ψ (PeL e p + b • e)) b :=
  ((hC.FE_continuous he).comp ((continuous_const).add (continuous_id.smul continuous_const))
    ).integral_hasStrictDerivAt 0 b

lemma ae_ne_zero_real : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 :=
  compl_mem_ae_iff.mpr (measure_singleton 0)

/-- Off the plane, at fixed height `τ ≠ 0`, `p ↦ FE e ψ (P p + τ e)` has derivative `kw1 ∘ P`. -/
lemma C1H.hasFDerivAt_FE_slice (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1)
    {τ : ℝ} (hτ : τ ≠ 0) (p : Eu d) :
    HasFDerivAt (fun p => FE e ψ (PeL e p + τ • e))
      ((kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)) p := by
  have hs : 0 < τ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hτ))
  have e1 : (fun p => FE e ψ (PeL e p + τ • e)) =
      fun p => kw0 univ (wK d) ψ (τ ^ 2) (PeL e p + τ • e) := by
    funext p
    simp only [FE, Wb, inner_PeL_add he, if_pos hs]
  rw [e1]
  have hin : HasFDerivAt (fun p => PeL e p + τ • e) (PeL e) p :=
    (PeL e).hasFDerivAt.add_const _
  exact (wh_hasFDerivAt_kw0 hC.continuous.aestronglyMeasurable
    (fun y _ => hC.b0 y) hs _).comp p hin

lemma C1H.DQE_meas (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (p : Eu d) (A : Set ℝ) :
    AEStronglyMeasurable (fun τ => (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e))
      (volume.restrict A) := by
  have hco : ContinuousOn (fun τ : ℝ => (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e))
      {0}ᶜ := by
    intro τ hτ
    have hτ0 : τ ≠ 0 := hτ
    have hs : 0 < τ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hτ0))
    have h1 := hC.W_cf2 hs (PeL e p + τ • e)
    have hm : ContinuousAt (fun τ : ℝ => (τ ^ 2, PeL e p + τ • e)) τ := by fun_prop
    have h2 : ContinuousAt (fun τ : ℝ => kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)) τ :=
      ContinuousAt.comp (f := fun τ : ℝ => (τ ^ 2, PeL e p + τ • e))
        (g := fun v : ℝ × Eu d => kw1 univ wK1 ψ v.1 v.2) h1 hm
    have h3 : Continuous fun B : Eu d →L[ℝ] ℝ => B.comp (PeL e) :=
      ((ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)).continuous
    exact (h3.continuousAt.comp h2).continuousWithinAt
  have h := hco.aestronglyMeasurable (μ := volume) (isOpen_compl_singleton.measurableSet)
  rw [restrict_compl_singleton] at h
  exact h.restrict

lemma C1H.DQE_bound (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} {τ : ℝ} (hτ : τ ≠ 0) (p : Eu d) :
    ‖(kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)‖ ≤ wA d * M1 * ‖PeL e‖ := by
  have hs : 0 < τ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hτ))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hC.kw1_norm_le hs _) (norm_nonneg _))

/-- `p`-derivative of `QE`. -/
lemma C1H.QE_hasFDerivAt_p (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1)
    (p₀ : Eu d) (b : ℝ) : HasFDerivAt (fun p => QE e ψ p b) (DQE e ψ p₀ b) p₀ := by
  have hFc : ∀ p, Continuous fun τ : ℝ => FE e ψ (PeL e p + τ • e) := fun p =>
    (hC.FE_continuous he).comp ((continuous_const).add (continuous_id.smul continuous_const))
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p τ => FE e ψ (PeL e p + τ • e))
    (F' := fun p τ => (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e))
    (bound := fun _ => wA d * M1 * ‖PeL e‖) (Filter.univ_mem) ?_ ((hFc p₀).intervalIntegrable _ _)
    (hC.DQE_meas p₀ _) ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun p => (hFc p).aestronglyMeasurable
  · filter_upwards [ae_ne_zero_real] with τ hτ _ p _
    exact hC.DQE_bound hτ p
  · filter_upwards [ae_ne_zero_real] with τ hτ _ p _
    exact hC.hasFDerivAt_FE_slice he hτ p

end Ext3

section Ext4

variable {d : ℕ}

variable [IFacts d]

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

/-- The integrand of `DQE`. -/
noncomputable def DQI (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (τ : ℝ) : Eu d →L[ℝ] ℝ :=
  (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)

lemma DQE_eq (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (b : ℝ) :
    DQE e ψ p b = ∫ τ in (0 : ℝ)..b, DQI e ψ p τ := rfl

lemma C1H.DQI_contP (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} {τ : ℝ} (hτ : τ ≠ 0) :
    Continuous fun p => DQI e ψ p τ := by
  have hs : 0 < τ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hτ))
  have h3 : Continuous fun B : Eu d →L[ℝ] ℝ => B.comp (PeL e) :=
    ((ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)).continuous
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have h1 := hC.W_cf2 hs (PeL e p + τ • e)
  have hm : ContinuousAt (fun p : Eu d => (τ ^ 2, PeL e p + τ • e)) p := by fun_prop
  have h2 : ContinuousAt (fun p : Eu d => kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)) p :=
    ContinuousAt.comp (f := fun p : Eu d => (τ ^ 2, PeL e p + τ • e))
      (g := fun v : ℝ × Eu d => kw1 univ wK1 ψ v.1 v.2) h1 hm
  exact h3.continuousAt.comp h2

lemma C1H.DQI_ae_bound (hC : C1H d μ M0 M1 H ψ ψ1) (e p : Eu d) :
    ∀ᵐ τ : ℝ ∂volume, ‖DQI e ψ p τ‖ ≤ wA d * M1 * ‖PeL e‖ := by
  filter_upwards [ae_ne_zero_real] with τ hτ
  exact hC.DQE_bound hτ p

lemma C1H.DQI_ii (hC : C1H d μ M0 M1 H ψ ψ1) (e p : Eu d) (a b : ℝ) :
    IntervalIntegrable (fun τ => DQI e ψ p τ) volume a b := by
  refine (intervalIntegrable_const : IntervalIntegrable
    (fun _ : ℝ => wA d * M1 * ‖PeL e‖) volume a b).mono_fun (hC.DQE_meas p _) ?_
  filter_upwards [ae_restrict_of_ae (hC.DQI_ae_bound e p)] with τ hτ
  exact hτ.trans (Real.le_norm_self _)

lemma C1H.DQE_sub_le (hC : C1H d μ M0 M1 H ψ ψ1) (e p : Eu d) (b b' : ℝ) :
    ‖DQE e ψ p b' - DQE e ψ p b‖ ≤ wA d * M1 * ‖PeL e‖ * |b' - b| := by
  rw [DQE_eq, DQE_eq, intervalIntegral.integral_interval_sub_left (hC.DQI_ii e p 0 b')
    (hC.DQI_ii e p 0 b)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
  filter_upwards [hC.DQI_ae_bound e p] with τ hτ _ using hτ

lemma C1H.DQE_contP (hC : C1H d μ M0 M1 H ψ ψ1) (e : Eu d) (b : ℝ) :
    Continuous fun p => DQE e ψ p b := by
  refine intervalIntegral.continuous_of_dominated_interval
    (bound := fun _ => wA d * M1 * ‖PeL e‖) (fun p => hC.DQE_meas p _) (fun p => ?_)
    intervalIntegrable_const ?_
  · filter_upwards [hC.DQI_ae_bound e p] with τ hτ _ using hτ
  · filter_upwards [ae_ne_zero_real] with τ hτ _ using hC.DQI_contP hτ

lemma C1H.DQE_contAt (hC : C1H d μ M0 M1 H ψ ψ1) (e p₀ : Eu d) (b₀ : ℝ) :
    ContinuousAt (fun v : Eu d × ℝ => DQE e ψ v.1 v.2) (p₀, b₀) := by
  have h1 : Tendsto (fun v : Eu d × ℝ => DQE e ψ v.1 b₀) (𝓝 (p₀, b₀)) (𝓝 (DQE e ψ p₀ b₀)) :=
    ((hC.DQE_contP e b₀).tendsto p₀).comp continuousAt_fst
  have h2 : Tendsto (fun v : Eu d × ℝ => DQE e ψ v.1 v.2 - DQE e ψ v.1 b₀) (𝓝 (p₀, b₀))
      (𝓝 0) := by
    refine squeeze_zero_norm (fun v => hC.DQE_sub_le e v.1 b₀ v.2) ?_
    have hc : Continuous fun v : Eu d × ℝ => wA d * M1 * ‖PeL e‖ * |v.2 - b₀| := by fun_prop
    have := hc.tendsto (p₀, b₀)
    simpa using this
  have h3 := h1.add h2
  simp only [add_sub_cancel, add_zero] at h3
  exact h3

lemma smulRight_one_cont' : Continuous fun a : ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight a := by
  have e : (fun a : ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight a) = fun a => a • (1 : ℝ →L[ℝ] ℝ) := by
    funext a; ext; simp
  rw [e]; exact continuous_id.smul continuous_const

lemma C1H.QE_df2 (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1) (u : Eu d × ℝ) :
    ∀ᶠ v : Eu d × ℝ in 𝓝 u, HasFDerivAt (fun b => QE e ψ v.1 b)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (FE e ψ (PeL e v.1 + v.2 • e))) v.2 :=
  Eventually.of_forall fun v => (hC.QE_hasStrictDerivAt_b he v.1 v.2).hasDerivAt.hasFDerivAt

lemma C1H.QE_cf2 (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1) (u : Eu d × ℝ) :
    ContinuousAt (fun v : Eu d × ℝ =>
      (1 : ℝ →L[ℝ] ℝ).smulRight (FE e ψ (PeL e v.1 + v.2 • e))) u := by
  have hin : Continuous fun v : Eu d × ℝ => PeL e v.1 + v.2 • e := by fun_prop
  exact (smulRight_one_cont'.comp ((hC.FE_continuous he).comp hin)).continuousAt

lemma C1H.QE_strict (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1)
    (p₀ : Eu d) (b₀ : ℝ) :
    HasStrictFDerivAt (Function.uncurry fun p b => QE e ψ p b)
      ((DQE e ψ p₀ b₀).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (FE e ψ (PeL e p₀ + b₀ • e))))
      (p₀, b₀) :=
  hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (p₀, b₀))
    (f := fun p b => QE e ψ p b) (f₁ := fun p b => DQE e ψ p b)
    (f₂ := fun p b => (1 : ℝ →L[ℝ] ℝ).smulRight (FE e ψ (PeL e p + b • e)))
    (Eventually.of_forall fun v => hC.QE_hasFDerivAt_p he v.1 v.2)
    (hC.QE_df2 he _) (hC.DQE_contAt e p₀ b₀) (hC.QE_cf2 he (p₀, b₀))

/-- Derivative of the extension. -/
noncomputable def DEXT (e : Eu d) (ψ : Eu d → ℝ) (x : Eu d) : Eu d →L[ℝ] ℝ :=
  DQE e ψ x (inner ℝ x e) + FE e ψ x • innerSL ℝ e

lemma PeL_add_inner (e x : Eu d) : PeL e x + inner ℝ x e • e = x := by
  rw [PeL_apply, sub_add_cancel]

lemma EXT_eq_comp (e : Eu d) (ψ : Eu d → ℝ) :
    EXT e ψ = (Function.uncurry fun p b => QE e ψ p b) ∘ fun x => (x, innerSL ℝ e x) := by
  funext x
  show QE e ψ x (inner ℝ x e) = QE e ψ x (innerSL ℝ e x)
  rw [innerSL_apply_apply, real_inner_comm]

lemma C1H.EXT_strict (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1) (x₀ : Eu d) :
    HasStrictFDerivAt (EXT e ψ) (DEXT e ψ x₀) x₀ := by
  have ht : innerSL ℝ e x₀ = inner ℝ x₀ e := by rw [innerSL_apply_apply, real_inner_comm]
  have hin : HasStrictFDerivAt (fun x : Eu d => (x, innerSL ℝ e x))
      ((ContinuousLinearMap.id ℝ (Eu d)).prod (innerSL ℝ e)) x₀ :=
    (hasStrictFDerivAt_id x₀).prodMk (innerSL ℝ e).hasStrictFDerivAt
  have hQ := hC.QE_strict he x₀ (innerSL ℝ e x₀)
  have hc := hQ.comp x₀ hin
  rw [EXT_eq_comp]
  refine hc.congr_fderiv ?_
  ext v
  simp only [DEXT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ht,
    PeL_add_inner]
  ring

lemma C1H.DEXT_continuous (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (he : ‖e‖ = 1) :
    Continuous (DEXT e ψ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hm : Continuous fun x : Eu d => (x, inner ℝ x e) := by fun_prop
  have h1 : ContinuousAt (fun x : Eu d => DQE e ψ x (inner ℝ x e)) x :=
    ContinuousAt.comp (f := fun x : Eu d => (x, inner ℝ x e))
      (g := fun v : Eu d × ℝ => DQE e ψ v.1 v.2) (hC.DQE_contAt e x _) hm.continuousAt
  exact h1.add (((hC.FE_continuous he).smul continuous_const).continuousAt)

lemma EXT_plane {e x : Eu d} (hx : inner ℝ x e = 0) : EXT e ψ x = 0 := by
  unfold EXT QE; rw [hx]; simp

lemma DEXT_plane {e x : Eu d} (hx : inner ℝ x e = 0) :
    DEXT e ψ x = ψ x • innerSL ℝ e := by
  unfold DEXT DQE; rw [hx, FE_plane hx]; simp

end Ext4

section Ext5

variable {d : ℕ}

variable [IFacts d]

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

lemma tau_rpow_facts {τ : ℝ} (hτ : 0 < τ) (μ : ℝ) :
    (τ ^ 2) ^ (-(1 / 2 : ℝ)) * (4 * τ ^ 2) ^ (μ / 2) = 4 ^ (μ / 2) * τ ^ (μ - 1) := by
  rw [Real.mul_rpow (by norm_num) (sq_nonneg τ)]
  have h1 : (τ ^ 2) ^ (-(1 / 2 : ℝ)) = τ ^ (-1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; norm_num
  have h2 : (τ ^ 2) ^ (μ / 2) = τ ^ μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; congr 1; push_cast; ring
  rw [h1, h2, Real.rpow_sub hτ, Real.rpow_one, Real.rpow_neg_one]
  ring

/-- `‖kw2 ψ s y‖ ≤ wA s^(-1/2) H gm (4s)^(μ/2)` (transfer to `kw1` of the Hölder `ψ1 · v`). -/
lemma C1H.kw2_norm_le (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s : ℝ} (hs : 0 < s) (y : Eu d) :
    ‖kw2 univ wK2 ψ s y‖ ≤ wA d * s ^ (-(1 / 2 : ℝ)) * H * (gm d * (4 * s) ^ (μ / 2)) := by
  have hgm : 0 ≤ gm d := by unfold gm; positivity
  have hK0 : 0 ≤ wA d * s ^ (-(1 / 2 : ℝ)) * H * (gm d * (4 * s) ^ (μ / 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg wA_nonneg (rpow_nonneg hs.le _)) hC.hH)
      (mul_nonneg hgm (rpow_nonneg (by positivity) _))
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK0 (norm_nonneg u)) fun v => ?_
  rw [kw2_trans hC.hd hC.cont hC.b0 hC.b1 hs y u v]
  have h1 := wh_kw1_hol (hC.holV v) (hC.measV v) hμ0 hμ2 hs (mem_univ y)
  have h2 := (kw1 univ wK1 (fun y => ψ1 y v) s y).le_opNorm u
  calc ‖kw1 univ wK1 (fun y => ψ1 y v) s y u‖
      ≤ ‖kw1 univ wK1 (fun y => ψ1 y v) s y‖ * ‖u‖ := h2
    _ ≤ (wA d * s ^ (-(1 / 2 : ℝ)) * (H * ‖v‖) * (gm d * (4 * s) ^ (μ / 2))) * ‖u‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg u)
    _ = wA d * s ^ (-(1 / 2 : ℝ)) * H * (gm d * (4 * s) ^ (μ / 2)) * ‖u‖ * ‖v‖ := by ring

/-- The constant of the `τ^(μ-1)` bound. -/
noncomputable def KB (d : ℕ) (μ H : ℝ) : ℝ := wA d * H * gm d * 4 ^ (μ / 2)

lemma C1H.KB_nonneg (hC : C1H d μ M0 M1 H ψ ψ1) : 0 ≤ KB d μ H := by
  have hgm : 0 ≤ gm d := by unfold gm; positivity
  unfold KB
  exact mul_nonneg (mul_nonneg (mul_nonneg wA_nonneg hC.hH) hgm) (rpow_nonneg (by norm_num) _)

lemma C1H.kw2_tau_le (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {τ : ℝ} (hτ : 0 < τ) (y : Eu d) :
    ‖kw2 univ wK2 ψ (τ ^ 2) y‖ ≤ KB d μ H * τ ^ (μ - 1) := by
  refine (hC.kw2_norm_le hμ0 hμ2 (by positivity) y).trans (le_of_eq ?_)
  unfold KB
  have := tau_rpow_facts hτ μ
  calc wA d * (τ ^ 2) ^ (-(1 / 2 : ℝ)) * H * (gm d * (4 * τ ^ 2) ^ (μ / 2))
      = wA d * H * gm d * ((τ ^ 2) ^ (-(1 / 2 : ℝ)) * (4 * τ ^ 2) ^ (μ / 2)) := by ring
    _ = wA d * H * gm d * 4 ^ (μ / 2) * τ ^ (μ - 1) := by rw [this]; ring

/-- Joint continuity of `kw2 ψ` at positive times (entrywise via the transfer). -/
lemma C1H.kw2_contAt (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (y₀ : Eu d) :
    ContinuousAt (fun q : ℝ × Eu d => kw2 univ wK2 ψ q.1 q.2) (s₀, y₀) := by
  rw [continuousAt_clm_apply]; intro u
  rw [continuousAt_clm_apply]; intro v
  have hev : ∀ᶠ q : ℝ × Eu d in 𝓝 (s₀, y₀), 0 < q.1 :=
    (continuous_fst.tendsto (s₀, y₀)).eventually (Ioi_mem_nhds hs₀)
  have h1 : ContinuousAt (fun q : ℝ × Eu d => kw1 univ wK1 (fun y => ψ1 y v) q.1 q.2 u)
      (s₀, y₀) :=
    (ContinuousLinearMap.apply ℝ ℝ u).continuous.continuousAt.comp
      (kw1_contAt (hC.holV v) (hC.measV v) hμ0 hμ2 hs₀ y₀)
  refine h1.congr ?_
  filter_upwards [hev] with q hq
  exact (kw2_trans hC.hd hC.cont hC.b0 hC.b1 hq q.2 u v).symm

/-- Joint continuity of `DQI` off `τ = 0`. -/
lemma C1H.DQI_contAt (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} {p₀ : Eu d} {b₀ : ℝ}
    (hb₀ : b₀ ≠ 0) : ContinuousAt (fun v : Eu d × ℝ => DQI e ψ v.1 v.2) (p₀, b₀) := by
  have hs : 0 < b₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hb₀))
  have h3 : Continuous fun B : Eu d →L[ℝ] ℝ => B.comp (PeL e) :=
    ((ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)).continuous
  have h1 := hC.W_cf2 hs (PeL e p₀ + b₀ • e)
  have hm : ContinuousAt (fun v : Eu d × ℝ => (v.2 ^ 2, PeL e v.1 + v.2 • e)) (p₀, b₀) := by
    fun_prop
  have h2 : ContinuousAt (fun v : Eu d × ℝ => kw1 univ wK1 ψ (v.2 ^ 2) (PeL e v.1 + v.2 • e))
      (p₀, b₀) :=
    ContinuousAt.comp (f := fun v : Eu d × ℝ => (v.2 ^ 2, PeL e v.1 + v.2 • e))
      (g := fun v : ℝ × Eu d => kw1 univ wK1 ψ v.1 v.2) h1 hm
  exact h3.continuousAt.comp h2

lemma C1H.DQI_contOn_tau (hC : C1H d μ M0 M1 H ψ ψ1) (e p : Eu d) :
    ContinuousOn (fun τ => DQI e ψ p τ) {0}ᶜ := by
  intro τ hτ
  have h := hC.DQI_contAt (e := e) (p₀ := p) (hb₀ := hτ)
  have hm : ContinuousAt (fun τ : ℝ => (p, τ)) τ := by fun_prop
  exact (ContinuousAt.comp (f := fun τ : ℝ => (p, τ))
    (g := fun v : Eu d × ℝ => DQI e ψ v.1 v.2) h hm).continuousWithinAt

/-- `p`-derivative of `DQI` (for `τ ≠ 0`). -/
noncomputable def D2QI (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (τ : ℝ) :
    Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)).comp
    ((kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e))

lemma C1H.hasFDerivAt_DQI (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} {τ : ℝ} (hτ : τ ≠ 0)
    (p : Eu d) : HasFDerivAt (fun p => DQI e ψ p τ) (D2QI e ψ p τ) p := by
  have hs : 0 < τ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hτ))
  have hin : HasFDerivAt (fun p => PeL e p + τ • e) (PeL e) p :=
    (PeL e).hasFDerivAt.add_const _
  have hk := (wh_hasFDerivAt_kw1 hC.continuous.aestronglyMeasurable
    (fun y _ => hC.b0 y) hs (PeL e p + τ • e)).comp p hin
  exact ((ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)).hasFDerivAt.comp p hk

lemma norm_flipP_le (e : Eu d) :
    ‖(ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip (PeL e)‖ ≤ ‖PeL e‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun B => ?_
  show ‖B.comp (PeL e)‖ ≤ ‖PeL e‖ * ‖B‖
  rw [mul_comm]; exact ContinuousLinearMap.opNorm_comp_le _ _

lemma C1H.D2QI_le (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {e : Eu d}
    {τ : ℝ} (hτ : 0 < τ) (p : Eu d) :
    ‖D2QI e ψ p τ‖ ≤ ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1) := by
  unfold D2QI
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 := norm_flipP_le e
  have h2 := (ContinuousLinearMap.opNorm_comp_le
    (kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)) (PeL e)).trans
    (mul_le_mul_of_nonneg_right (hC.kw2_tau_le hμ0 hμ2 hτ (PeL e p + τ • e)) (norm_nonneg _))
  calc _ ≤ ‖PeL e‖ * (KB d μ H * τ ^ (μ - 1) * ‖PeL e‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
    _ = ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1) := by ring

lemma C1H.D2QI_meas (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (e p : Eu d)
    (A : Set ℝ) : AEStronglyMeasurable (fun τ => D2QI e ψ p τ) (volume.restrict A) := by
  have hco : ContinuousOn (fun τ : ℝ => D2QI e ψ p τ) {0}ᶜ := by
    intro τ hτ
    have hτ0 : τ ≠ 0 := hτ
    have hs : 0 < τ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hτ0))
    have h1 := hC.kw2_contAt hμ0 hμ2 hs (PeL e p + τ • e)
    have hm : ContinuousAt (fun τ : ℝ => (τ ^ 2, PeL e p + τ • e)) τ := by fun_prop
    have h2 : ContinuousAt (fun τ : ℝ => kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)) τ :=
      ContinuousAt.comp (f := fun τ : ℝ => (τ ^ 2, PeL e p + τ • e))
        (g := fun v : ℝ × Eu d => kw2 univ wK2 ψ v.1 v.2) h1 hm
    exact (continuousAt_const.clm_comp (h2.clm_comp continuousAt_const)).continuousWithinAt
  have h := hco.aestronglyMeasurable (μ := volume) (isOpen_compl_singleton.measurableSet)
  rw [restrict_compl_singleton] at h
  exact h.restrict

/-- Second `p`-derivative of `QE`. -/
noncomputable def D2QE (e : Eu d) (ψ : Eu d → ℝ) (p : Eu d) (b : ℝ) :
    Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ τ in (0 : ℝ)..b, D2QI e ψ p τ

lemma rpow_ii {μ : ℝ} (hμ0 : 0 < μ) (C a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => C * τ ^ (μ - 1)) volume a b :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C

lemma C1H.DQE_hasFDerivAt_p2 (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2)
    {e : Eu d} {b : ℝ} (hb : 0 < b) (p₀ : Eu d) :
    HasFDerivAt (fun p => DQE e ψ p b) (D2QE e ψ p₀ b) p₀ := by
  have hI : ∀ τ, τ ∈ Set.uIoc (0 : ℝ) b → 0 < τ := fun τ hτ => by
    rw [uIoc_of_le hb.le] at hτ; exact hτ.1
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p τ => DQI e ψ p τ) (F' := fun p τ => D2QI e ψ p τ)
    (bound := fun τ => ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1)) (Filter.univ_mem)
    (Eventually.of_forall fun p => hC.DQE_meas p _) (hC.DQI_ii e p₀ 0 b)
    (hC.D2QI_meas hμ0.le hμ2 e p₀ _) ?_ (rpow_ii hμ0 _ _ _) ?_
  · exact Eventually.of_forall fun τ hτ p _ => hC.D2QI_le hμ0.le hμ2 (hI τ hτ) p
  · exact Eventually.of_forall fun τ hτ p _ => hC.hasFDerivAt_DQI (hI τ hτ).ne' p

lemma C1H.DQE_hasFDerivAt_b (hC : C1H d μ M0 M1 H ψ ψ1) {e : Eu d} (p : Eu d) {b : ℝ}
    (hb : b ≠ 0) :
    HasFDerivAt (fun b => DQE e ψ p b) ((1 : ℝ →L[ℝ] ℝ).smulRight (DQI e ψ p b)) b := by
  have hd : HasDerivAt (fun b => ∫ τ in (0 : ℝ)..b, DQI e ψ p τ) (DQI e ψ p b) b :=
    intervalIntegral.integral_hasDerivAt_right (hC.DQI_ii e p 0 b)
      ((hC.DQI_contOn_tau e p).stronglyMeasurableAtFilter isOpen_compl_singleton b hb)
      ((hC.DQI_contOn_tau e p).continuousAt (isOpen_compl_singleton.mem_nhds hb))
  exact hd.hasFDerivAt

lemma C1H.D2QI_ii (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (e p : Eu d)
    {c : ℝ} (hc : 0 ≤ c) : IntervalIntegrable (fun τ => D2QI e ψ p τ) volume 0 c := by
  refine (rpow_ii hμ0 (‖PeL e‖ ^ 2 * KB d μ H) 0 c).mono_fun' (hC.D2QI_meas hμ0.le hμ2 e p _) ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun τ hτ => ?_)
  rw [uIoc_of_le hc] at hτ
  exact hC.D2QI_le hμ0.le hμ2 hτ.1 p

lemma C1H.D2QE_sub_le (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d}
    (p : Eu d) {b₀ b : ℝ} (hb₀ : 0 < b₀) (hb : b₀ / 2 ≤ b) :
    ‖D2QE e ψ p b - D2QE e ψ p b₀‖ ≤
      ‖PeL e‖ ^ 2 * KB d μ H * (b₀ / 2) ^ (μ - 1) * |b - b₀| := by
  have hμ2 : μ ≤ 2 := by linarith
  unfold D2QE
  rw [intervalIntegral.integral_interval_sub_left (hC.D2QI_ii hμ0 hμ2 e p (by linarith))
    (hC.D2QI_ii hμ0 hμ2 e p hb₀.le)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (Eventually.of_forall fun τ hτ => ?_)
  have h2 : b₀ / 2 ≤ b₀ ⊓ b := le_inf (by linarith) hb
  have hτ1 : b₀ / 2 < τ := lt_of_le_of_lt h2 hτ.1
  have hτ0 : 0 < τ := by linarith
  refine (hC.D2QI_le hμ0.le hμ2 hτ0 p).trans ?_
  have hK : 0 ≤ ‖PeL e‖ ^ 2 * KB d μ H := mul_nonneg (sq_nonneg _) hC.KB_nonneg
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by linarith) hτ1.le (by linarith)) hK

lemma C1H.D2QI_contP (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {e : Eu d}
    {τ : ℝ} (hτ : τ ≠ 0) : Continuous fun p => D2QI e ψ p τ := by
  have hs : 0 < τ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hτ))
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have h1 := hC.kw2_contAt hμ0 hμ2 hs (PeL e p + τ • e)
  have hm : ContinuousAt (fun p : Eu d => (τ ^ 2, PeL e p + τ • e)) p := by fun_prop
  have h2 : ContinuousAt (fun p : Eu d => kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)) p :=
    ContinuousAt.comp (f := fun p : Eu d => (τ ^ 2, PeL e p + τ • e))
      (g := fun v : ℝ × Eu d => kw2 univ wK2 ψ v.1 v.2) h1 hm
  exact continuousAt_const.clm_comp (h2.clm_comp continuousAt_const)

lemma C1H.D2QE_contP (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (e : Eu d)
    {b : ℝ} (hb : 0 < b) : Continuous fun p => D2QE e ψ p b := by
  have hI : ∀ τ, τ ∈ Set.uIoc (0 : ℝ) b → 0 < τ := fun τ hτ => by
    rw [uIoc_of_le hb.le] at hτ; exact hτ.1
  exact intervalIntegral.continuous_of_dominated_interval
    (bound := fun τ => ‖PeL e‖ ^ 2 * KB d μ H * τ ^ (μ - 1))
    (fun p => hC.D2QI_meas hμ0.le hμ2 e p _)
    (fun p => Eventually.of_forall fun τ hτ => hC.D2QI_le hμ0.le hμ2 (hI τ hτ) p)
    (rpow_ii hμ0 _ _ _)
    (Eventually.of_forall fun τ hτ => hC.D2QI_contP hμ0.le hμ2 (hI τ hτ).ne')

lemma C1H.D2QE_contAt (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (e p₀ : Eu d) {b₀ : ℝ} (hb₀ : 0 < b₀) :
    ContinuousAt (fun v : Eu d × ℝ => D2QE e ψ v.1 v.2) (p₀, b₀) := by
  have hμ2 : μ ≤ 2 := by linarith
  have h1 : Tendsto (fun v : Eu d × ℝ => D2QE e ψ v.1 b₀) (𝓝 (p₀, b₀))
      (𝓝 (D2QE e ψ p₀ b₀)) :=
    ((hC.D2QE_contP hμ0 hμ2 e hb₀).tendsto p₀).comp continuousAt_fst
  have hev : ∀ᶠ v : Eu d × ℝ in 𝓝 (p₀, b₀), b₀ / 2 ≤ v.2 :=
    (continuous_snd.tendsto (p₀, b₀)).eventually (Ici_mem_nhds (by linarith))
  have h2 : Tendsto (fun v : Eu d × ℝ => D2QE e ψ v.1 v.2 - D2QE e ψ v.1 b₀) (𝓝 (p₀, b₀))
      (𝓝 0) := by
    refine squeeze_zero_norm' (hev.mono fun v hv => hC.D2QE_sub_le hμ0 hμ1 v.1 hb₀ hv) ?_
    have hc : Continuous fun v : Eu d × ℝ =>
        ‖PeL e‖ ^ 2 * KB d μ H * (b₀ / 2) ^ (μ - 1) * |v.2 - b₀| := by fun_prop
    simpa using hc.tendsto (p₀, b₀)
  have h3 := h1.add h2
  simp only [add_sub_cancel, add_zero] at h3
  exact h3

lemma smulRight_one_contV : Continuous fun X : Eu d →L[ℝ] ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight X := by
  have e : (fun X : Eu d →L[ℝ] ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight X) =
      fun X => ContinuousLinearMap.smulRightL ℝ ℝ (Eu d →L[ℝ] ℝ) 1 X := by
    funext X; ext; simp
  rw [e]; exact (ContinuousLinearMap.smulRightL ℝ ℝ (Eu d →L[ℝ] ℝ) 1).continuous

lemma C1H.DQE_strict2 (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : Eu d}
    {p₀ : Eu d} {b₀ : ℝ} (hb₀ : 0 < b₀) :
    HasStrictFDerivAt (Function.uncurry fun p b => DQE e ψ p b)
      ((D2QE e ψ p₀ b₀).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (DQI e ψ p₀ b₀))) (p₀, b₀) := by
  have hμ2 : μ ≤ 2 := by linarith
  have hev : ∀ᶠ v : Eu d × ℝ in 𝓝 (p₀, b₀), 0 < v.2 :=
    (continuous_snd.tendsto (p₀, b₀)).eventually (Ioi_mem_nhds hb₀)
  exact hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (p₀, b₀))
    (f := fun p b => DQE e ψ p b) (f₁ := fun p b => D2QE e ψ p b)
    (f₂ := fun p b => (1 : ℝ →L[ℝ] ℝ).smulRight (DQI e ψ p b))
    (hev.mono fun v hv => hC.DQE_hasFDerivAt_p2 hμ0 hμ2 hv v.1)
    (hev.mono fun v hv => hC.DQE_hasFDerivAt_b v.1 hv.ne')
    (hC.D2QE_contAt hμ0 hμ1 e p₀ hb₀)
    (smulRight_one_contV.continuousAt.comp (hC.DQI_contAt hb₀.ne'))

/-- Second derivative of the extension (open side). -/
noncomputable def D2EXT (e : Eu d) (ψ : Eu d → ℝ) (x : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  D2QE e ψ x (inner ℝ x e) + (innerSL ℝ e).smulRight (DQI e ψ x (inner ℝ x e))
    + (DFE e ψ x).smulRight (innerSL ℝ e)

lemma DEXT_eq_fun (e : Eu d) (ψ : Eu d → ℝ) : DEXT e ψ = fun x =>
    (Function.uncurry fun p b => DQE e ψ p b) ((fun x : Eu d => (x, innerSL ℝ e x)) x)
      + FE e ψ x • innerSL ℝ e := by
  funext x
  show DQE e ψ x (inner ℝ x e) + FE e ψ x • innerSL ℝ e =
    DQE e ψ x (innerSL ℝ e x) + FE e ψ x • innerSL ℝ e
  rw [innerSL_apply_apply, real_inner_comm]

lemma C1H.DEXT_hasFDerivAt (hC : C1H d μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {e : Eu d} {x₀ : Eu d} (hx₀ : 0 < inner ℝ x₀ e) :
    HasFDerivAt (DEXT e ψ) (D2EXT e ψ x₀) x₀ := by
  have hμ2 : μ ≤ 2 := by linarith
  have ht : innerSL ℝ e x₀ = inner ℝ x₀ e := by rw [innerSL_apply_apply, real_inner_comm]
  have hin : HasFDerivAt (fun x : Eu d => (x, innerSL ℝ e x))
      ((ContinuousLinearMap.id ℝ (Eu d)).prod (innerSL ℝ e)) x₀ :=
    (hasFDerivAt_id x₀).prodMk (innerSL ℝ e).hasFDerivAt
  have hpos : 0 < innerSL ℝ e x₀ := by rw [ht]; exact hx₀
  have hQ := (hC.DQE_strict2 hμ0 hμ1 (e := e) (p₀ := x₀) hpos).hasFDerivAt
  have hc := hQ.comp x₀ hin
  have hF := (hC.hasFDerivAt_FE hμ0.le hμ2 hx₀.ne').smul_const (innerSL ℝ e)
  have hsum := hc.add hF
  rw [DEXT_eq_fun]
  refine hsum.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  simp only [D2EXT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ht]

end Ext5

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
  let gm : ℝ := (1 + 2 * 2 ^ ((d : ℝ) / 2));
  let HolderOnS : {d : ℕ} → (S : Set (EuclideanSpace ℝ (Fin d))) → (μ M0 Hh : ℝ) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → Prop := fun {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (μ M0 Hh : ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) => (0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ);
  let kw0 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K t x y);
  let kw1 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K1 t x y);
  let kw2 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K2 t x y);
  let lap2 : {d : ℕ} → (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → ℝ := fun {d : ℕ} (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) => (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1));
  let Ip : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ);
  let ge : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (rexp (-(a * ‖z‖ ^ 2)));
  let gK1 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((-(2 * a) * ge a z) • Ip z);
  let gK2 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (ge a z • ((4 * a ^ 2) • (Ip z).smulRight (Ip z) - (2 * a) • Ip));
  let hN : (t : ℝ) → ℝ := fun (t : ℝ) => ((π * (2 * t)) ^ (-((d : ℝ) / 2)));
  let wK : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (G (2 * t) (x - y));
  let wK1 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK1 (1 / (2 * t)) (x - y));
  let wK2 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK2 (1 / (2 * t)) (x - y));
  let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
  let C1H : (μ M0 M1 H : ℝ) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → Prop := fun (μ M0 M1 H : ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) => ((∀ y, HasFDerivAt ψ (ψ1 y) y) ∧ Continuous ψ1 ∧ (∀ y, |ψ y| ≤ M0) ∧ (∀ y, ‖ψ1 y‖ ≤ M1) ∧ (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H);
  let Wb : (h : EuclideanSpace ℝ (Fin d) → ℝ) → (s : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (h : EuclideanSpace ℝ (Fin d) → ℝ) (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (if 0 < s then kw0 univ (wK) h s x else h x);
  let FE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) => (Wb ψ (inner ℝ y e ^ 2) y);
  let DFE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) => ((inner ℝ y e * lap2 (kw2 univ wK2 ψ (inner ℝ y e ^ 2) y)) • innerSL ℝ e + kw1 univ wK1 ψ (inner ℝ y e ^ 2) y);
  let PeL : (e : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := fun (e : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - (innerSL ℝ e).smulRight e);
  let QE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (b : ℝ) → ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (b : ℝ) => (∫ τ in (0 : ℝ)..b, FE e ψ (PeL e p + τ • e));
  let EXT : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) => (QE e ψ x (inner ℝ x e));
  let DQE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (b : ℝ) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (b : ℝ) => (∫ τ in (0 : ℝ)..b, (kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e));
  let DQI : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (τ : ℝ) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (τ : ℝ) => ((kw1 univ wK1 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e));
  let DEXT : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) => (DQE e ψ x (inner ℝ x e) + FE e ψ x • innerSL ℝ e);
  let KB : (μ H : ℝ) → ℝ := fun (μ H : ℝ) => (wA * H * gm * 4 ^ (μ / 2));
  let D2QI : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (τ : ℝ) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (τ : ℝ) => (((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) ℝ).flip (PeL e)).comp ((kw2 univ wK2 ψ (τ ^ 2) (PeL e p + τ • e)).comp (PeL e)));
  let D2QE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (p : EuclideanSpace ℝ (Fin d)) → (b : ℝ) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (p : EuclideanSpace ℝ (Fin d)) (b : ℝ) => (∫ τ in (0 : ℝ)..b, D2QI e ψ p τ);
  let D2EXT : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) => (D2QE e ψ x (inner ℝ x e) + (innerSL ℝ e).smulRight (DQI e ψ x (inner ℝ x e)) + (DFE e ψ x).smulRight (innerSL ℝ e));
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1), Continuous ψ) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (v : EuclideanSpace ℝ (Fin d)), HolderOnS univ μ (M1 * ‖v‖) (H * ‖v‖) (fun y => ψ1 y v)) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (v : EuclideanSpace ℝ (Fin d)), AEStronglyMeasurable (fun y => ψ1 y v) (volume.restrict (univ : Set (EuclideanSpace ℝ (Fin d))))) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) {s : ℝ} (hs : 0 < s) (y : EuclideanSpace ℝ (Fin d)), lap2 (kw2 univ wK2 ψ s y) = ∑ i : Fin d, kw1 univ wK1 (fun z => ψ1 z (EuclideanSpace.single i 1)) s y (EuclideanSpace.single i 1)) ∧
    (∀ (e x : EuclideanSpace ℝ (Fin d)), PeL e x + inner ℝ x e • e = x) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x₀ : EuclideanSpace ℝ (Fin d)), HasStrictFDerivAt (EXT e ψ) (DEXT e ψ x₀) x₀) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1), Continuous (DEXT e ψ)) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {e x : EuclideanSpace ℝ (Fin d)} (hx : inner ℝ x e = 0), EXT e ψ x = 0) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {e x : EuclideanSpace ℝ (Fin d)} (hx : inner ℝ x e = 0), DEXT e ψ x = ψ x • innerSL ℝ e) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1), 0 ≤ KB μ H) ∧
    (∀ (e : EuclideanSpace ℝ (Fin d)), ‖(ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) ℝ).flip (PeL e)‖ ≤ ‖PeL e‖) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {e : EuclideanSpace ℝ (Fin d)} {τ : ℝ} (hτ : 0 < τ) (p : EuclideanSpace ℝ (Fin d)), ‖D2QI e ψ p τ‖ ≤ ‖PeL e‖ ^ 2 * KB μ H * τ ^ (μ - 1)) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (e p : EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : 0 ≤ c), IntervalIntegrable (fun τ => D2QI e ψ p τ) volume 0 c) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {μ M0 M1 H : ℝ} (hC : C1H μ M0 M1 H ψ ψ1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : EuclideanSpace ℝ (Fin d)} {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : 0 < inner ℝ x₀ e), HasFDerivAt (DEXT e ψ) (D2EXT e ψ x₀) x₀) := by
  intro d
  intro G gm HolderOnS kw0 kw1 kw2 lap2 Ip ge gK1 gK2 hN wK wK1 wK2 wA C1H Wb FE DFE PeL QE EXT DQE DQI DEXT KB D2QI D2QE D2EXT
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_kw1_trans, f_kw2_trans, f_kw3_trans, f_wh_hasDerivAt_kw0_t, f_wh_hasFDerivAt_kw0, f_wh_hasFDerivAt_kw1, f_wh_hasFDerivAt_kw2, f_wh_kw0_le, f_wh_kw0_sub_h, f_wh_kw0_time_diff, f_wh_kw1_hol, f_wh_kw1_le, f_wh_kw1_time_le, f_wh_kw2_hol, f_wh_kw1_lip⟩ := @EthierKurtz.heat_kernel_smoothing_estimates d
  haveI : ObliqueLib.IFacts d := ⟨f_wA_nonneg, f_kw1_trans, f_kw2_trans, f_wh_hasDerivAt_kw0_t, f_wh_hasFDerivAt_kw0, f_wh_hasFDerivAt_kw1, f_wh_kw0_le, f_wh_kw0_sub_h, f_wh_kw0_time_diff, f_wh_kw1_hol, f_wh_kw1_le, f_wh_kw1_time_le, f_wh_kw1_lip⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ ψ1 μ M0 M1 H hC; exact ObliqueLib.C1H.continuous hC
  · intro ψ ψ1 μ M0 M1 H hC v; exact ObliqueLib.C1H.holV hC v
  · intro ψ ψ1 μ M0 M1 H hC v; exact ObliqueLib.C1H.measV hC v
  · intro ψ ψ1 μ M0 M1 H hC s hs y; exact ObliqueLib.C1H.lap2_kw2_eq hC hs y
  · intro e x; exact ObliqueLib.PeL_add_inner e x
  · intro ψ ψ1 μ M0 M1 H hC e he x₀; exact ObliqueLib.C1H.EXT_strict hC he x₀
  · intro ψ ψ1 μ M0 M1 H hC e he; exact ObliqueLib.C1H.DEXT_continuous hC he
  · intro ψ e x hx; exact ObliqueLib.EXT_plane hx
  · intro ψ e x hx; exact ObliqueLib.DEXT_plane hx
  · intro ψ ψ1 μ M0 M1 H hC; exact ObliqueLib.C1H.KB_nonneg hC
  · intro e; exact ObliqueLib.norm_flipP_le e
  · intro ψ ψ1 μ M0 M1 H hC hμ0 hμ2 e τ hτ p; exact ObliqueLib.C1H.D2QI_le hC hμ0 hμ2 hτ p
  · intro ψ ψ1 μ M0 M1 H hC hμ0 hμ2 e p c hc; exact ObliqueLib.C1H.D2QI_ii hC hμ0 hμ2 e p hc
  · intro ψ ψ1 μ M0 M1 H hC hμ0 hμ1 e x₀ hx₀; exact ObliqueLib.C1H.DEXT_hasFDerivAt hC hμ0 hμ1 hx₀
