-- Prove2me | solution 1 for EthierKurtz.heat_extension_holder_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T14:46:29.137216+00:00
-- url     : https://prove2.me/submissions/45cd6941-1088-4da1-b7dd-8b2bcdf408ca

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

theorem KHyp.b1 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.1

theorem KHyp.b2 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.2.1

theorem KHyp.b3 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.2.2.1

end KHypDef

/-- `h` is bounded by `M0` and `μ`-Hölder with constant `Hh` on `S`. -/
def HolderOnS {d : ℕ} (S : Set (Eu d)) (μ M0 Hh : ℝ) (h : Eu d → ℝ) : Prop :=
  0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ

/-- Trace of a bilinear form in the standard basis (twice the generator `Δ/2` acts as `lap2/2`). -/
noncomputable def lap2 {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

lemma abs_lap2_le {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : |lap2 B| ≤ d * ‖B‖ := by
  unfold lap2
  calc |∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)|
      ≤ ∑ i : Fin d, |B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖B‖ := Finset.sum_le_sum fun i _ => by
        have := B.le_opNorm₂ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i 1)
        rw [EuclideanSpace.norm_single, norm_one, mul_one, mul_one] at this
        rwa [← Real.norm_eq_abs]
    _ = d * ‖B‖ := by simp

section C1Hdef

/-- `ψ` is bounded, differentiable with bounded, continuous, `μ`-Hölder derivative `ψ1`. -/
@[reducible] def C1H (d : ℕ) (μ M0 M1 H : ℝ) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) : Prop :=
  (∀ y, HasFDerivAt ψ (ψ1 y) y) ∧ Continuous ψ1 ∧ (∀ y, |ψ y| ≤ M0) ∧ (∀ y, ‖ψ1 y‖ ≤ M1) ∧
    (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H

variable {d : ℕ} {μ M0 M1 H : ℝ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)}

theorem C1H.hd (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, HasFDerivAt ψ (ψ1 y) y := hC.1

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

end Ext2

section Ext3

variable {d : ℕ}

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

end Ext3

section Ext4

variable {d : ℕ}

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

end Ext4

section Ext5

variable {d : ℕ}

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

end Ext5

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  wA_nonneg : 0 ≤ wA d
  wh_hasFDerivAt_kw0 : ∀ {h : Eu d → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (Eu d)), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw0 univ (wK d) h t) (kw1 univ wK1 h t x) x
  wh_hasFDerivAt_kw1 : ∀ {h : Eu d → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (Eu d)), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw1 univ wK1 h t) (kw2 univ wK2 h t x) x
  wh_kw0_sub_h : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), |kw0 univ (wK d) h t x - h x| ≤ wA d * Hh * (gm d * (4 * t) ^ (μ / 2))
  wh_kw0_time_diff : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), kw0 univ (wK d) h s' x - kw0 univ (wK d) h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 univ wK2 h σ x)
  wh_kw1_hol : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), ‖kw1 univ wK1 h t x‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * Hh * (gm d * (4 * t) ^ (μ / 2))
  wh_kw1_time_le : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ (univ : Set (Eu d))), ‖kw1 univ wK1 h s' x - kw1 univ wK1 h s x‖ ≤ (1 / 2 : ℝ) * (‖lap2L d‖ * (wA d * s ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (4 * s') ^ (μ / 2)))) * (s' - s)
  wh_kw2_hol : ∀ {h : Eu d → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))), ‖kw2 univ wK2 h t x‖ ≤ wA d * t ^ (-(1 : ℝ)) * Hh * (gm d * (4 * t) ^ (μ / 2))

end IFk

export IFacts (wA_nonneg wh_hasFDerivAt_kw0 wh_hasFDerivAt_kw1 wh_kw0_sub_h wh_kw0_time_diff wh_kw1_hol wh_kw1_time_le wh_kw2_hol)

section Ext5_dup

variable {d : ℕ}

variable {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {μ M0 M1 H : ℝ}

variable [IFacts d]

lemma tau_rpow_facts {τ : ℝ} (hτ : 0 < τ) (μ : ℝ) :
    (τ ^ 2) ^ (-(1 / 2 : ℝ)) * (4 * τ ^ 2) ^ (μ / 2) = 4 ^ (μ / 2) * τ ^ (μ - 1) := by
  rw [Real.mul_rpow (by norm_num) (sq_nonneg τ)]
  have h1 : (τ ^ 2) ^ (-(1 / 2 : ℝ)) = τ ^ (-1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; norm_num
  have h2 : (τ ^ 2) ^ (μ / 2) = τ ^ μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; congr 1; push_cast; ring
  rw [h1, h2, Real.rpow_sub hτ, Real.rpow_one, Real.rpow_neg_one]
  ring

end Ext5_dup

section Hol1

variable {d : ℕ} {h : Eu d → ℝ} {μ M Hh : ℝ}

variable [IFacts d]

lemma sq_rpow_half_mu (t μ : ℝ) : (t ^ 2) ^ (μ / 2) = |t| ^ μ := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]; congr 1; push_cast; ring

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

lemma Wb_zero (h : Eu d → ℝ) (y : Eu d) : Wb h 0 y = h y := by
  unfold Wb; rw [if_neg (lt_irrefl 0)]

lemma Wb_sub_h (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ))
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {s : ℝ} (hs : 0 ≤ s) (y : Eu d) :
    |Wb h s y - h y| ≤ wA d * Hh * (gm d * (4 * s) ^ (μ / 2)) := by
  rcases hs.lt_or_eq with hs0 | hs0
  · unfold Wb; rw [if_pos hs0]
    exact wh_kw0_sub_h hhol hm hμ0 hμ2 hs0 (mem_univ y)
  · subst hs0
    rw [Wb_zero, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg wA_nonneg hhol.2.1)
      (mul_nonneg (gm_pos d).le (rpow_nonneg (by norm_num) _))

lemma kw0_lip_hol (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s : ℝ} (hs : 0 < s) (x x' : Eu d) :
    |kw0 univ (wK d) h s x - kw0 univ (wK d) h s x'| ≤
      wA d * s ^ (-(1 / 2 : ℝ)) * Hh * (gm d * (4 * s) ^ (μ / 2)) * ‖x - x'‖ := by
  rw [← Real.norm_eq_abs]
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (wh_hasFDerivAt_kw0 hm hhol.2.2.1 hs z).hasFDerivWithinAt)
    (fun z hz => wh_kw1_hol hhol hm hμ0 hμ2 hs hz) convex_univ (mem_univ x')
    (mem_univ x)

/-- Constant of the time-Hölder bound. -/
noncomputable def cTm (d : ℕ) (μ : ℝ) : ℝ := (d / μ + 1) * wA d * gm d * 4 ^ (μ / 2)

lemma Wb_time_hol (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2)
    {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') (y : Eu d) :
    |Wb h s' y - Wb h s y| ≤ cTm d μ * Hh * (s' ^ (μ / 2) - s ^ (μ / 2)) := by
  have hA := wA_nonneg (d := d)
  have hgm := gm_pos d
  have hH := hhol.2.1
  have h4 : 0 ≤ (4 : ℝ) ^ (μ / 2) := rpow_nonneg (by norm_num) _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmono : s ^ (μ / 2) ≤ s' ^ (μ / 2) := rpow_le_rpow hs hss (by linarith)
  have hdiff := sub_nonneg.mpr hmono
  rcases hs.lt_or_eq with hs0 | hs0
  · have hs' : 0 < s' := lt_of_lt_of_le hs0 hss
    unfold Wb
    rw [if_pos hs', if_pos hs0, wh_kw0_time_diff hhol hm hs0 hss (mem_univ y),
      ← Real.norm_eq_abs]
    have hI : IntervalIntegrable (fun σ : ℝ =>
        (1 / 2 : ℝ) * (d * (wA d * Hh * gm d * 4 ^ (μ / 2))) * σ ^ (μ / 2 - 1)) volume s s' :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
    refine (intervalIntegral.norm_integral_le_of_norm_le hss
      (Eventually.of_forall fun σ hσ => ?_) hI).trans ?_
    · have hσ0 : 0 < σ := lt_trans hs0 hσ.1
      have hk := wh_kw2_hol hhol hm hμ0.le hμ2 hσ0 (mem_univ y)
      have hl := abs_lap2_le (kw2 univ wK2 h σ y)
      have he : σ ^ (-(1 : ℝ)) * (gm d * (4 * σ) ^ (μ / 2)) =
          gm d * 4 ^ (μ / 2) * σ ^ (μ / 2 - 1) := by
        rw [Real.mul_rpow (by norm_num) hσ0.le, Real.rpow_sub hσ0, Real.rpow_one,
          Real.rpow_neg_one]
        field_simp
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc (1 / 2 : ℝ) * |lap2 (kw2 univ wK2 h σ y)|
          ≤ (1 / 2) * (d * ‖kw2 univ wK2 h σ y‖) := by gcongr
        _ ≤ (1 / 2) * (d * (wA d * σ ^ (-(1 : ℝ)) * Hh * (gm d * (4 * σ) ^ (μ / 2)))) := by
            gcongr
        _ = (1 / 2) * (d * (wA d * Hh * gm d * 4 ^ (μ / 2))) * σ ^ (μ / 2 - 1) := by
            rw [show wA d * σ ^ (-(1 : ℝ)) * Hh * (gm d * (4 * σ) ^ (μ / 2)) =
              wA d * Hh * (σ ^ (-(1 : ℝ)) * (gm d * (4 * σ) ^ (μ / 2))) by ring, he]
            ring
    · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
      have e : μ / 2 - 1 + 1 = μ / 2 := by ring
      rw [e]
      unfold cTm
      have hμne : μ ≠ 0 := hμ0.ne'
      have e2 : (1 / 2 : ℝ) * (d * (wA d * Hh * gm d * 4 ^ (μ / 2))) *
          ((s' ^ (μ / 2) - s ^ (μ / 2)) / (μ / 2)) =
          d / μ * wA d * gm d * 4 ^ (μ / 2) * Hh * (s' ^ (μ / 2) - s ^ (μ / 2)) := by
        field_simp
      rw [e2]
      have h5 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA hgm.le) h4) hH) hdiff
      have e3 : (d / μ + 1) * wA d * gm d * 4 ^ (μ / 2) * Hh * (s' ^ (μ / 2) - s ^ (μ / 2)) =
          d / μ * wA d * gm d * 4 ^ (μ / 2) * Hh * (s' ^ (μ / 2) - s ^ (μ / 2)) +
          wA d * gm d * 4 ^ (μ / 2) * Hh * (s' ^ (μ / 2) - s ^ (μ / 2)) := by ring
      rw [e3]; linarith
  · subst hs0
    rw [zero_rpow (by linarith : μ / 2 ≠ 0), sub_zero, Wb_zero]
    refine (Wb_sub_h hhol hm hμ0.le hμ2 hss y).trans ?_
    rw [Real.mul_rpow (by norm_num) hss]
    unfold cTm
    have hdμ : 0 ≤ (d : ℝ) / μ := div_nonneg hd0 hμ0.le
    have h6 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hdμ hA) hgm.le) h4) hH)
      (rpow_nonneg hss (μ / 2))
    have e3 : (d / μ + 1) * wA d * gm d * 4 ^ (μ / 2) * Hh * s' ^ (μ / 2) =
        d / μ * wA d * gm d * 4 ^ (μ / 2) * Hh * s' ^ (μ / 2) +
        wA d * Hh * (gm d * (4 ^ (μ / 2) * s' ^ (μ / 2))) := by ring
    rw [e3]; linarith

lemma Wb_time_hol' (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2)
    {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') (y : Eu d) :
    |Wb h s' y - Wb h s y| ≤ cTm d μ * Hh * |s' ^ (μ / 2) - s ^ (μ / 2)| := by
  rcases le_total s s' with hh | hh
  · have := Wb_time_hol hhol hm hμ0 hμ2 hs hh y
    rwa [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hs hh (by linarith)))]
  · have := Wb_time_hol hhol hm hμ0 hμ2 hs' hh y
    rw [abs_sub_comm, abs_sub_comm (s' ^ _)]
    rwa [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hs' hh (by linarith)))]

/-- Constant of the Hölder bound of the parabolic extension. -/
noncomputable def cH (d : ℕ) (μ : ℝ) : ℝ :=
  (2 + 2 ^ μ) * wA d * gm d * 4 ^ (μ / 2) + 1 + cTm d μ

lemma abs_inner_sub_le {e : Eu d} (he : ‖e‖ = 1) (x x' : Eu d) :
    abs (abs (inner ℝ x e) - abs (inner ℝ x' e)) ≤ ‖x - x'‖ := by
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  rw [← inner_sub_left]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [he, mul_one]

/-- **Hölder continuity of the parabolic heat extension.** -/
lemma FE_hol (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {e : Eu d} (he : ‖e‖ = 1) (x x' : Eu d) :
    |FE e h x - FE e h x'| ≤ cH d μ * Hh * ‖x - x'‖ ^ μ := by
  have hμ2 : μ ≤ 2 := by linarith
  have hA := wA_nonneg (d := d)
  have hgm := gm_pos d
  have hH := hhol.2.1
  have h4 : 0 ≤ (4 : ℝ) ^ (μ / 2) := rpow_nonneg (by norm_num) _
  have h2μ : 0 ≤ (2 : ℝ) ^ μ := rpow_nonneg (by norm_num) _
  have hcT : 0 ≤ cTm d μ := by
    unfold cTm
    have : 0 ≤ (d : ℝ) / μ + 1 := by have := div_nonneg (Nat.cast_nonneg d) hμ0.le; linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg this hA) hgm.le) h4
  have hK0 : 0 ≤ wA d * gm d * 4 ^ (μ / 2) * Hh :=
    mul_nonneg (mul_nonneg (mul_nonneg hA hgm.le) h4) hH
  have hcH : 0 ≤ cH d μ := by
    unfold cH
    have : 0 ≤ (2 + 2 ^ μ) * wA d * gm d * 4 ^ (μ / 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hA) hgm.le) h4
    linarith
  have htt := abs_inner_sub_le he x x'
  have hδ0 : 0 ≤ ‖x - x'‖ := norm_nonneg _
  have hδμ : 0 ≤ ‖x - x'‖ ^ μ := rpow_nonneg hδ0 _
  have hsub : ∀ y : Eu d,
      |FE e h y - h y| ≤ wA d * gm d * 4 ^ (μ / 2) * Hh * |inner ℝ y e| ^ μ := by
    intro y
    have := Wb_sub_h hhol hm hμ0.le hμ2 (sq_nonneg (inner ℝ y e)) y
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _), sq_rpow_half_mu] at this
    unfold FE
    linarith [show wA d * Hh * (gm d * (4 ^ (μ / 2) * |inner ℝ y e| ^ μ)) =
      wA d * gm d * 4 ^ (μ / 2) * Hh * |inner ℝ y e| ^ μ by ring]
  have hK1 : 0 ≤ wA d * gm d * 4 ^ (μ / 2) * Hh * ‖x - x'‖ ^ μ := mul_nonneg hK0 hδμ
  have hct : 0 ≤ cTm d μ * Hh * ‖x - x'‖ ^ μ := mul_nonneg (mul_nonneg hcT hH) hδμ
  rcases lt_or_ge (abs (inner ℝ x e)) ‖x - x'‖ with hlt | hge
  · -- near the plane: compare both with `h`
    have h1 := hsub x
    have h2 := hsub x'
    have h3 : |h x - h x'| ≤ Hh * ‖x - x'‖ ^ μ := hhol.2.2.2 x (mem_univ _) x' (mem_univ _)
    have hp1 : |inner ℝ x e| ^ μ ≤ ‖x - x'‖ ^ μ := rpow_le_rpow (abs_nonneg _) hlt.le hμ0.le
    have ht'le : |inner ℝ x' e| ≤ 2 * ‖x - x'‖ := by
      have := (abs_le.mp htt).1; linarith
    have hp2 : |inner ℝ x' e| ^ μ ≤ 2 ^ μ * ‖x - x'‖ ^ μ := by
      rw [← Real.mul_rpow (by norm_num) hδ0]; exact rpow_le_rpow (abs_nonneg _) ht'le hμ0.le
    have e1 : FE e h x - FE e h x' = (FE e h x - h x) + (h x - h x') - (FE e h x' - h x') := by
      ring
    rw [e1]
    have hm1 := mul_le_mul_of_nonneg_left hp1 hK0
    have hm2 := mul_le_mul_of_nonneg_left hp2 hK0
    have hfin : |(FE e h x - h x) + (h x - h x') - (FE e h x' - h x')| ≤
        |FE e h x - h x| + |h x - h x'| + |FE e h x' - h x'| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    unfold cH
    have e2 : ((2 + 2 ^ μ) * wA d * gm d * 4 ^ (μ / 2) + 1 + cTm d μ) * Hh * ‖x - x'‖ ^ μ =
        wA d * gm d * 4 ^ (μ / 2) * Hh * ‖x - x'‖ ^ μ
        + wA d * gm d * 4 ^ (μ / 2) * Hh * (2 ^ μ * ‖x - x'‖ ^ μ)
        + Hh * ‖x - x'‖ ^ μ + (wA d * gm d * 4 ^ (μ / 2) * Hh * ‖x - x'‖ ^ μ
        + cTm d μ * Hh * ‖x - x'‖ ^ μ) := by
      ring
    rw [e2]
    linarith
  · rcases hδ0.lt_or_eq with hδpos | hδz
    · -- away from the plane: space step at time `t²`, then time step at `x'`
      have htpos : 0 < |inner ℝ x e| := lt_of_lt_of_le hδpos hge
      have hq : inner ℝ x e ^ 2 = |inner ℝ x e| ^ 2 := (sq_abs _).symm
      have hs : 0 < inner ℝ x e ^ 2 := by rw [hq]; positivity
      have hWx : Wb h (inner ℝ x e ^ 2) x = kw0 univ (wK d) h (inner ℝ x e ^ 2) x := by
        unfold Wb; rw [if_pos hs]
      have hWx' : Wb h (inner ℝ x e ^ 2) x' = kw0 univ (wK d) h (inner ℝ x e ^ 2) x' := by
        unfold Wb; rw [if_pos hs]
      have hsp := kw0_lip_hol hhol hm hμ0.le hμ2 hs x x'
      have hfac : wA d * (inner ℝ x e ^ 2) ^ (-(1 / 2 : ℝ)) * Hh *
          (gm d * (4 * inner ℝ x e ^ 2) ^ (μ / 2)) * ‖x - x'‖ =
          wA d * gm d * 4 ^ (μ / 2) * Hh * (|inner ℝ x e| ^ (μ - 1) * ‖x - x'‖) := by
        rw [hq]
        have := tau_rpow_facts htpos μ
        calc _ = wA d * gm d * Hh * ((abs (inner ℝ x e) ^ 2) ^ (-(1 / 2 : ℝ)) *
              (4 * abs (inner ℝ x e) ^ 2) ^ (μ / 2)) * ‖x - x'‖ := by ring
          _ = _ := by rw [this]; ring
      rw [hfac] at hsp
      have hpow : |inner ℝ x e| ^ (μ - 1) * ‖x - x'‖ ≤ ‖x - x'‖ ^ μ := by
        have h1 : |inner ℝ x e| ^ (μ - 1) ≤ ‖x - x'‖ ^ (μ - 1) :=
          Real.rpow_le_rpow_of_nonpos hδpos hge (by linarith)
        calc |inner ℝ x e| ^ (μ - 1) * ‖x - x'‖ ≤ ‖x - x'‖ ^ (μ - 1) * ‖x - x'‖ :=
              mul_le_mul_of_nonneg_right h1 hδ0
          _ = ‖x - x'‖ ^ μ := by rw [← Real.rpow_add_one hδpos.ne']; ring_nf
      have htm := Wb_time_hol' hhol hm hμ0 hμ2 (sq_nonneg (inner ℝ x e))
        (sq_nonneg (inner ℝ x' e)) x'
      rw [sq_rpow_half_mu, sq_rpow_half_mu] at htm
      have hab := abs_rpow_sub_le (abs_nonneg (inner ℝ x' e)) (abs_nonneg (inner ℝ x e))
        hμ0.le hμ1
      have hab2 : abs (abs (inner ℝ x' e) - abs (inner ℝ x e)) ^ μ ≤ ‖x - x'‖ ^ μ := by
        rw [abs_sub_comm]; exact rpow_le_rpow (abs_nonneg _) htt hμ0.le
      have e1 : FE e h x - FE e h x' =
          (kw0 univ (wK d) h (inner ℝ x e ^ 2) x - kw0 univ (wK d) h (inner ℝ x e ^ 2) x') -
          (Wb h (inner ℝ x' e ^ 2) x' - Wb h (inner ℝ x e ^ 2) x') := by
        unfold FE; rw [hWx, hWx']; ring
      rw [e1]
      have hfin := abs_sub (kw0 univ (wK d) h (inner ℝ x e ^ 2) x -
        kw0 univ (wK d) h (inner ℝ x e ^ 2) x') (Wb h (inner ℝ x' e ^ 2) x' -
        Wb h (inner ℝ x e ^ 2) x')
      have hA1 := mul_le_mul_of_nonneg_left hpow hK0
      have hA2 : cTm d μ * Hh * abs (abs (inner ℝ x' e) ^ μ - abs (inner ℝ x e) ^ μ) ≤
          cTm d μ * Hh * ‖x - x'‖ ^ μ :=
        mul_le_mul_of_nonneg_left (hab.trans hab2) (mul_nonneg hcT hH)
      unfold cH
      have e2 : ((2 + 2 ^ μ) * wA d * gm d * 4 ^ (μ / 2) + 1 + cTm d μ) * Hh * ‖x - x'‖ ^ μ =
          wA d * gm d * 4 ^ (μ / 2) * Hh * ‖x - x'‖ ^ μ + cTm d μ * Hh * ‖x - x'‖ ^ μ +
          ((1 + 2 ^ μ) * (wA d * gm d * 4 ^ (μ / 2) * Hh * ‖x - x'‖ ^ μ)
            + Hh * ‖x - x'‖ ^ μ) := by ring
      rw [e2]
      have h7 : 0 ≤ (1 + 2 ^ μ) * (wA d * gm d * 4 ^ (μ / 2) * Hh * ‖x - x'‖ ^ μ)
          + Hh * ‖x - x'‖ ^ μ :=
        add_nonneg (mul_nonneg (by linarith) hK1) (mul_nonneg hH hδμ)
      linarith
    · -- δ = 0
      have hxx : x = x' := sub_eq_zero.mp (norm_eq_zero.mp hδz.symm)
      rw [hxx, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hcH hH) (rpow_nonneg (norm_nonneg _) _)

end Hol1

section Hol2

variable {d : ℕ} {h : Eu d → ℝ} {μ M Hh : ℝ}

variable [IFacts d]

/-- `wA gm 4^(μ/2) Hh`. -/
noncomputable def KH1 (d : ℕ) (μ Hh : ℝ) : ℝ := wA d * gm d * 4 ^ (μ / 2) * Hh

lemma KH1_nonneg (hH : 0 ≤ Hh) : 0 ≤ KH1 d μ Hh :=
  mul_nonneg (mul_nonneg (mul_nonneg wA_nonneg (gm_pos d).le) (rpow_nonneg (by norm_num) _)) hH

lemma rpow_pred_mul_le {a δ μ : ℝ} (hδ : 0 < δ) (hda : δ ≤ a) (hμ1 : μ ≤ 1) :
    a ^ (μ - 1) * δ ≤ δ ^ μ := by
  have h1 : a ^ (μ - 1) ≤ δ ^ (μ - 1) := Real.rpow_le_rpow_of_nonpos hδ hda (by linarith)
  calc a ^ (μ - 1) * δ ≤ δ ^ (μ - 1) * δ := mul_le_mul_of_nonneg_right h1 hδ.le
    _ = δ ^ μ := by rw [← Real.rpow_add_one hδ.ne']; ring_nf

lemma mul_rpow_sub_two {a : ℝ} (ha : 0 < a) (μ : ℝ) : a * a ^ (μ - 2) = a ^ (μ - 1) := by
  rw [show μ - 1 = (μ - 2) + 1 by ring, Real.rpow_add_one ha.ne', mul_comm]

lemma tau_rpow_facts2 {a : ℝ} (ha : 0 < a) (μ : ℝ) :
    (a ^ 2) ^ (-(1 : ℝ)) * (4 * a ^ 2) ^ (μ / 2) = 4 ^ (μ / 2) * a ^ (μ - 2) := by
  rw [Real.mul_rpow (by norm_num) (sq_nonneg a), sq_rpow_half_mu, abs_of_pos ha,
    Real.rpow_neg_one, Real.rpow_sub ha, Real.rpow_two]
  ring

lemma kw1h_tau_le (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {a : ℝ} (ha : 0 < a) (y : Eu d) :
    ‖kw1 univ wK1 h (a ^ 2) y‖ ≤ KH1 d μ Hh * a ^ (μ - 1) := by
  refine (wh_kw1_hol hhol hm hμ0 hμ2 (by positivity) (mem_univ y)).trans
    (le_of_eq ?_)
  unfold KH1
  have := tau_rpow_facts ha μ
  calc wA d * (a ^ 2) ^ (-(1 / 2 : ℝ)) * Hh * (gm d * (4 * a ^ 2) ^ (μ / 2))
      = wA d * gm d * Hh * ((a ^ 2) ^ (-(1 / 2 : ℝ)) * (4 * a ^ 2) ^ (μ / 2)) := by ring
    _ = _ := by rw [this]; ring

lemma kw2h_tau_le (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {a : ℝ} (ha : 0 < a) (y : Eu d) :
    ‖kw2 univ wK2 h (a ^ 2) y‖ ≤ KH1 d μ Hh * a ^ (μ - 2) := by
  refine (wh_kw2_hol hhol hm hμ0 hμ2 (by positivity) (mem_univ y)).trans
    (le_of_eq ?_)
  unfold KH1
  have := tau_rpow_facts2 ha μ
  calc wA d * (a ^ 2) ^ (-(1 : ℝ)) * Hh * (gm d * (4 * a ^ 2) ^ (μ / 2))
      = wA d * gm d * Hh * ((a ^ 2) ^ (-(1 : ℝ)) * (4 * a ^ 2) ^ (μ / 2)) := by ring
    _ = _ := by rw [this]; ring

lemma kw1h_lip_tau (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {a : ℝ} (ha : 0 < a) (x x' : Eu d) :
    ‖kw1 univ wK1 h (a ^ 2) x - kw1 univ wK1 h (a ^ 2) x'‖ ≤
      KH1 d μ Hh * a ^ (μ - 2) * ‖x - x'‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (wh_hasFDerivAt_kw1 hm hhol.2.2.1 (by positivity) z).hasFDerivWithinAt)
    (fun z _ => kw2h_tau_le hhol hm hμ0 hμ2 ha z) convex_univ (mem_univ x') (mem_univ x)

lemma kw1h_time_aux (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    {a m M' : ℝ} (ha : 0 < a) (hmM : m ≤ M') (hma : a / 2 ≤ m) (hMa : M' ≤ 2 * a) (y : Eu d) :
    ‖kw1 univ wK1 h (M' ^ 2) y - kw1 univ wK1 h (m ^ 2) y‖ ≤
      16 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * a ^ (μ - 2) * (M' - m) := by
  have hμ2 : μ ≤ 2 := by linarith
  have hm0 : 0 < m := by linarith
  have hM0 : 0 < M' := by linarith
  have hA := wA_nonneg (d := d)
  have hgm := gm_pos d
  have hH := hhol.2.1
  have hL := norm_nonneg (lap2L d)
  have hk := wh_kw1_time_le hhol hm hμ0 hμ2 (s := m ^ 2) (s' := M' ^ 2)
    (by positivity) (pow_le_pow_left₀ hm0.le hmM 2) (x := y) one_pos (subset_univ _)
  refine hk.trans ?_
  have ha2 : 0 < a / 2 := by linarith
  have hP1 : (m ^ 2) ^ (-(3 / 2 : ℝ)) ≤ 8 / a ^ 3 := by
    have h1 : (m ^ 2) ^ (-(3 / 2 : ℝ)) ≤ ((a / 2) ^ 2) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (pow_le_pow_left₀ ha2.le hma 2) (by norm_num)
    have h2 : ((a / 2) ^ 2) ^ (-(3 / 2 : ℝ)) = 8 / a ^ 3 := by
      rw [← Real.rpow_natCast (a / 2) 2, ← Real.rpow_mul ha2.le]
      have e3 : ((2 : ℕ) : ℝ) * (-(3 / 2 : ℝ)) = -((3 : ℕ) : ℝ) := by norm_num
      rw [e3, Real.rpow_neg ha2.le, Real.rpow_natCast, div_pow, inv_div]
      norm_num
    linarith
  have hP2 : (4 * M' ^ 2) ^ (μ / 2) ≤ 4 ^ μ * a ^ μ := by
    have h1 : (4 * M' ^ 2) ^ (μ / 2) ≤ ((4 * a) ^ 2) ^ (μ / 2) := by
      refine rpow_le_rpow (by positivity) ?_ (by linarith)
      linarith [mul_le_mul hMa hMa hM0.le (by linarith : (0 : ℝ) ≤ 2 * a)]
    rw [sq_rpow_half_mu, abs_of_pos (by linarith : (0 : ℝ) < 4 * a),
      Real.mul_rpow (by norm_num) ha.le] at h1
    exact h1
  have hP3 : M' ^ 2 - m ^ 2 ≤ 4 * a * (M' - m) := by nlinarith
  have hP1n : 0 ≤ (m ^ 2) ^ (-(3 / 2 : ℝ)) := rpow_nonneg (sq_nonneg _) _
  have hP2n : 0 ≤ (4 * M' ^ 2) ^ (μ / 2) := rpow_nonneg (by positivity) _
  have hP3n : 0 ≤ M' ^ 2 - m ^ 2 := by nlinarith
  have hQ1n : 0 ≤ 8 / a ^ 3 := by positivity
  have hQ2n : 0 ≤ (4 : ℝ) ^ μ * a ^ μ := by positivity
  have hC0 : 0 ≤ (1 / 2 : ℝ) * ‖lap2L d‖ * wA d * Hh * gm d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hA) hH) hgm.le
  calc (1 / 2 : ℝ) * (‖lap2L d‖ * (wA d * (m ^ 2) ^ (-(3 / 2 : ℝ)) * Hh *
        (gm d * (4 * M' ^ 2) ^ (μ / 2)))) * (M' ^ 2 - m ^ 2)
      = ((1 / 2 : ℝ) * ‖lap2L d‖ * wA d * Hh * gm d) * ((m ^ 2) ^ (-(3 / 2 : ℝ)) *
          ((4 * M' ^ 2) ^ (μ / 2) * (M' ^ 2 - m ^ 2))) := by ring
    _ ≤ ((1 / 2 : ℝ) * ‖lap2L d‖ * wA d * Hh * gm d) * (8 / a ^ 3 *
          (4 ^ μ * a ^ μ * (4 * a * (M' - m)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hP1 (mul_le_mul hP2 hP3 hP3n hQ2n)
          (mul_nonneg hP2n hP3n) hQ1n) hC0
    _ = 16 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * a ^ (μ - 2) * (M' - m) := by
        rw [Real.rpow_sub ha, Real.rpow_two]
        field_simp
        ring

lemma kw1h_time_tau (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    {a a' : ℝ} (ha : 0 < a) (h1 : a / 2 ≤ a') (h2 : a' ≤ 2 * a) (y : Eu d) :
    ‖kw1 univ wK1 h (a' ^ 2) y - kw1 univ wK1 h (a ^ 2) y‖ ≤
      16 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * a ^ (μ - 2) * |a' - a| := by
  rcases le_total a a' with hh | hh
  · rw [abs_of_nonneg (sub_nonneg.mpr hh)]
    exact kw1h_time_aux hhol hm hμ0 hμ1 ha hh (by linarith) h2 y
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hh)]
    exact kw1h_time_aux hhol hm hμ0 hμ1 ha hh h1 (by linarith) y

/-- The normal-derivative term. -/
noncomputable def TK (e : Eu d) (h : Eu d → ℝ) (x : Eu d) : Eu d →L[ℝ] ℝ :=
  inner ℝ x e • kw1 univ wK1 h (inner ℝ x e ^ 2) x

lemma TK_le (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2)
    (e x : Eu d) : ‖TK e h x‖ ≤ KH1 d μ Hh * |inner ℝ x e| ^ μ := by
  have hK := KH1_nonneg (d := d) (μ := μ) hhol.2.1
  rcases (abs_nonneg (inner ℝ x e)).lt_or_eq with hpos | hz
  · unfold TK
    rw [norm_smul, Real.norm_eq_abs, ← sq_abs]
    have := kw1h_tau_le hhol hm hμ0.le hμ2 hpos x
    calc |inner ℝ x e| * ‖kw1 univ wK1 h (|inner ℝ x e| ^ 2) x‖
        ≤ |inner ℝ x e| * (KH1 d μ Hh * |inner ℝ x e| ^ (μ - 1)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = KH1 d μ Hh * (|inner ℝ x e| * |inner ℝ x e| ^ (μ - 1)) := by ring
      _ = KH1 d μ Hh * |inner ℝ x e| ^ μ := by
          have h := Real.rpow_add_one hpos.ne' (μ - 1)
          rw [sub_add_cancel] at h
          rw [h]; ring
  · have h0 : inner ℝ x e = 0 := abs_eq_zero.mp hz.symm
    unfold TK; rw [h0, zero_smul, norm_zero]
    exact mul_nonneg hK (rpow_nonneg (abs_nonneg _) _)

/-- Constant of the Hölder bound of `TK` (per unit `Hh`). -/
noncomputable def cTK (d : ℕ) (μ : ℝ) : ℝ :=
  5 * wA d * gm d * 4 ^ (μ / 2) + 32 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ

/-- **Hölder continuity of the normal-derivative term.** -/
lemma TK_hol (hhol : HolderOnS univ μ M Hh h)
    (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {e : Eu d} (he : ‖e‖ = 1) (x x' : Eu d) :
    ‖TK e h x - TK e h x'‖ ≤ cTK d μ * Hh * ‖x - x'‖ ^ μ := by
  have hμ2 : μ ≤ 2 := by linarith
  have hA := wA_nonneg (d := d)
  have hgm := gm_pos d
  have hH := hhol.2.1
  have hL := norm_nonneg (lap2L d)
  have hK := KH1_nonneg (d := d) (μ := μ) hhol.2.1
  have h4 : 0 ≤ (4 : ℝ) ^ μ := rpow_nonneg (by norm_num) _
  have hδ0 : 0 ≤ ‖x - x'‖ := norm_nonneg _
  have hδμ : 0 ≤ ‖x - x'‖ ^ μ := rpow_nonneg hδ0 _
  have htt := abs_inner_sub_le he x x'
  have htt' : |inner ℝ x e - inner ℝ x' e| ≤ ‖x - x'‖ := by
    rw [← inner_sub_left]; refine (abs_real_inner_le_norm _ _).trans ?_; rw [he, mul_one]
  have hT2 : 0 ≤ 32 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * ‖x - x'‖ ^ μ := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hL hA) hgm.le) h4) hH) hδμ
    linarith [show 32 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * ‖x - x'‖ ^ μ =
      32 * (‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * ‖x - x'‖ ^ μ) by ring]
  have ecTK : cTK d μ * Hh * ‖x - x'‖ ^ μ = 5 * (KH1 d μ Hh * ‖x - x'‖ ^ μ) +
      32 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * ‖x - x'‖ ^ μ := by
    unfold cTK KH1; ring
  have hK1 : 0 ≤ KH1 d μ Hh * ‖x - x'‖ ^ μ := mul_nonneg hK hδμ
  rcases lt_or_ge (abs (inner ℝ x e)) (2 * ‖x - x'‖) with hlt | hge
  · -- near the plane: both terms are small
    have h1 := TK_le hhol hm hμ0 hμ2 e x
    have h2 := TK_le hhol hm hμ0 hμ2 e x'
    have ht'le : |inner ℝ x' e| ≤ 3 * ‖x - x'‖ := by
      have := (abs_le.mp htt).1; linarith
    have hp1 : |inner ℝ x e| ^ μ ≤ 2 * ‖x - x'‖ ^ μ := by
      calc |inner ℝ x e| ^ μ ≤ (2 * ‖x - x'‖) ^ μ :=
            rpow_le_rpow (abs_nonneg _) hlt.le hμ0.le
        _ = 2 ^ μ * ‖x - x'‖ ^ μ := Real.mul_rpow (by norm_num) hδ0
        _ ≤ 2 * ‖x - x'‖ ^ μ := mul_le_mul_of_nonneg_right
            (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hμ1) hδμ
    have hp2 : |inner ℝ x' e| ^ μ ≤ 3 * ‖x - x'‖ ^ μ := by
      calc |inner ℝ x' e| ^ μ ≤ (3 * ‖x - x'‖) ^ μ := rpow_le_rpow (abs_nonneg _) ht'le hμ0.le
        _ = 3 ^ μ * ‖x - x'‖ ^ μ := Real.mul_rpow (by norm_num) hδ0
        _ ≤ 3 * ‖x - x'‖ ^ μ := mul_le_mul_of_nonneg_right
            (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hμ1) hδμ
    have hm1 := mul_le_mul_of_nonneg_left hp1 hK
    have hm2 := mul_le_mul_of_nonneg_left hp2 hK
    have := norm_sub_le (TK e h x) (TK e h x')
    rw [ecTK]
    linarith
  · rcases hδ0.lt_or_eq with hδpos | hδz
    · set a := |inner ℝ x e| with ha_def
      set a' := |inner ℝ x' e| with ha'_def
      have hapos : 0 < a := by linarith
      have hda : ‖x - x'‖ ≤ a := by linarith
      have ha'1 : a / 2 ≤ a' := by have := (abs_le.mp htt).2; linarith
      have ha'2 : a' ≤ 2 * a := by have := (abs_le.mp htt).1; linarith
      have ha'pos : 0 < a' := by linarith
      have hsx : inner ℝ x e ^ 2 = a ^ 2 := (sq_abs _).symm
      have hsx' : inner ℝ x' e ^ 2 = a' ^ 2 := (sq_abs _).symm
      have e1 : TK e h x - TK e h x' =
          (inner ℝ x e - inner ℝ x' e) • kw1 univ wK1 h (a ^ 2) x
          + inner ℝ x' e • (kw1 univ wK1 h (a ^ 2) x - kw1 univ wK1 h (a ^ 2) x')
          - inner ℝ x' e • (kw1 univ wK1 h (a' ^ 2) x' - kw1 univ wK1 h (a ^ 2) x') := by
        have hs1 : inner ℝ x e • kw1 univ wK1 h (a ^ 2) x - inner ℝ x' e • kw1 univ wK1 h (a ^ 2) x
            = (inner ℝ x e - inner ℝ x' e) • kw1 univ wK1 h (a ^ 2) x := (sub_smul _ _ _).symm
        unfold TK; rw [hsx, hsx', ← hs1]; simp only [smul_sub]; abel
      rw [e1]
      have b1 : ‖(inner ℝ x e - inner ℝ x' e) • kw1 univ wK1 h (a ^ 2) x‖ ≤
          KH1 d μ Hh * ‖x - x'‖ ^ μ := by
        rw [norm_smul, Real.norm_eq_abs]
        have := kw1h_tau_le hhol hm hμ0.le hμ2 hapos x
        calc |inner ℝ x e - inner ℝ x' e| * ‖kw1 univ wK1 h (a ^ 2) x‖
            ≤ ‖x - x'‖ * (KH1 d μ Hh * a ^ (μ - 1)) := mul_le_mul htt' this (norm_nonneg _) hδ0
          _ = KH1 d μ Hh * (a ^ (μ - 1) * ‖x - x'‖) := by ring
          _ ≤ KH1 d μ Hh * ‖x - x'‖ ^ μ :=
              mul_le_mul_of_nonneg_left (rpow_pred_mul_le hδpos hda hμ1) hK
      have b2 : ‖inner ℝ x' e • (kw1 univ wK1 h (a ^ 2) x - kw1 univ wK1 h (a ^ 2) x')‖ ≤
          2 * (KH1 d μ Hh * ‖x - x'‖ ^ μ) := by
        rw [norm_smul, Real.norm_eq_abs, ← ha'_def]
        have := kw1h_lip_tau hhol hm hμ0.le hμ2 hapos x x'
        calc a' * ‖kw1 univ wK1 h (a ^ 2) x - kw1 univ wK1 h (a ^ 2) x'‖
            ≤ (2 * a) * (KH1 d μ Hh * a ^ (μ - 2) * ‖x - x'‖) :=
              mul_le_mul ha'2 this (norm_nonneg _) (by linarith)
          _ = 2 * (KH1 d μ Hh * ((a * a ^ (μ - 2)) * ‖x - x'‖)) := by ring
          _ ≤ 2 * (KH1 d μ Hh * ‖x - x'‖ ^ μ) := by
              rw [mul_rpow_sub_two hapos]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (rpow_pred_mul_le hδpos hda hμ1) hK) (by norm_num)
      have b3 : ‖inner ℝ x' e • (kw1 univ wK1 h (a' ^ 2) x' - kw1 univ wK1 h (a ^ 2) x')‖ ≤
          32 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * ‖x - x'‖ ^ μ := by
        rw [norm_smul, Real.norm_eq_abs, ← ha'_def]
        have := kw1h_time_tau hhol hm hμ0.le hμ1 hapos ha'1 ha'2 x'
        have hC : 0 ≤ 16 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh := by
          have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hL hA) hgm.le) h4) hH
          linarith [show 16 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh =
            16 * (‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh) by ring]
        have hdd : |a' - a| ≤ ‖x - x'‖ := by rw [abs_sub_comm]; exact htt
        calc a' * ‖kw1 univ wK1 h (a' ^ 2) x' - kw1 univ wK1 h (a ^ 2) x'‖
            ≤ (2 * a) * (16 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * a ^ (μ - 2) * ‖x - x'‖) := by
              refine mul_le_mul ha'2 (this.trans ?_) (norm_nonneg _) (by linarith)
              exact mul_le_mul_of_nonneg_left hdd
                (mul_nonneg hC (rpow_nonneg hapos.le _))
          _ = 2 * (16 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh) * ((a * a ^ (μ - 2)) * ‖x - x'‖) := by
              ring
          _ ≤ 2 * (16 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh) * ‖x - x'‖ ^ μ := by
              rw [mul_rpow_sub_two hapos]
              exact mul_le_mul_of_nonneg_left (rpow_pred_mul_le hδpos hda hμ1) (by linarith)
          _ = 32 * ‖lap2L d‖ * wA d * gm d * 4 ^ μ * Hh * ‖x - x'‖ ^ μ := by ring
      have hfin := norm_sub_le ((inner ℝ x e - inner ℝ x' e) • kw1 univ wK1 h (a ^ 2) x
          + inner ℝ x' e • (kw1 univ wK1 h (a ^ 2) x - kw1 univ wK1 h (a ^ 2) x'))
        (inner ℝ x' e • (kw1 univ wK1 h (a' ^ 2) x' - kw1 univ wK1 h (a ^ 2) x'))
      have hfin2 := norm_add_le ((inner ℝ x e - inner ℝ x' e) • kw1 univ wK1 h (a ^ 2) x)
        (inner ℝ x' e • (kw1 univ wK1 h (a ^ 2) x - kw1 univ wK1 h (a ^ 2) x'))
      rw [ecTK]
      linarith
    · have hxx : x = x' := sub_eq_zero.mp (norm_eq_zero.mp hδz.symm)
      have hnn : 0 ≤ cTK d μ * Hh * ‖x - x'‖ ^ μ := by rw [ecTK]; linarith
      calc ‖TK e h x - TK e h x'‖ = 0 := by rw [hxx, sub_self, norm_zero]
        _ ≤ _ := hnn

end Hol2

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
  let lap2L : (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := (∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))));
  let Ip : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ);
  let ge : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (rexp (-(a * ‖z‖ ^ 2)));
  let gK1 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((-(2 * a) * ge a z) • Ip z);
  let gK2 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (ge a z • ((4 * a ^ 2) • (Ip z).smulRight (Ip z) - (2 * a) • Ip));
  let hN : (t : ℝ) → ℝ := fun (t : ℝ) => ((π * (2 * t)) ^ (-((d : ℝ) / 2)));
  let wK : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (G (2 * t) (x - y));
  let wK1 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK1 (1 / (2 * t)) (x - y));
  let wK2 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK2 (1 / (2 * t)) (x - y));
  let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
  let Wb : (h : EuclideanSpace ℝ (Fin d) → ℝ) → (s : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (h : EuclideanSpace ℝ (Fin d) → ℝ) (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (if 0 < s then kw0 univ (wK) h s x else h x);
  let FE : (e : EuclideanSpace ℝ (Fin d)) → (ψ : EuclideanSpace ℝ (Fin d) → ℝ) → (y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) => (Wb ψ (inner ℝ y e ^ 2) y);
  let cTm : (μ : ℝ) → ℝ := fun (μ : ℝ) => ((d / μ + 1) * wA * gm * 4 ^ (μ / 2));
  let cH : (μ : ℝ) → ℝ := fun (μ : ℝ) => ((2 + 2 ^ μ) * wA * gm * 4 ^ (μ / 2) + 1 + cTm μ);
  let KH1 : (μ Hh : ℝ) → ℝ := fun (μ Hh : ℝ) => (wA * gm * 4 ^ (μ / 2) * Hh);
  let TK : (e : EuclideanSpace ℝ (Fin d)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e : EuclideanSpace ℝ (Fin d)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) => (inner ℝ x e • kw1 univ wK1 h (inner ℝ x e ^ 2) x);
  let cTK : (μ : ℝ) → ℝ := fun (μ : ℝ) => (5 * wA * gm * 4 ^ (μ / 2) + 32 * ‖lap2L‖ * wA * gm * 4 ^ μ);
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x x' : EuclideanSpace ℝ (Fin d)), |FE e h x - FE e h x'| ≤ cH μ * Hh * ‖x - x'‖ ^ μ) ∧
    (∀ {μ Hh : ℝ} (hH : 0 ≤ Hh), 0 ≤ KH1 μ Hh) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {a : ℝ} (ha : 0 < a) (y : EuclideanSpace ℝ (Fin d)), ‖kw2 univ wK2 h (a ^ 2) y‖ ≤ KH1 μ Hh * a ^ (μ - 2)) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M Hh : ℝ} (hhol : HolderOnS univ μ M Hh h) (hm : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x x' : EuclideanSpace ℝ (Fin d)), ‖TK e h x - TK e h x'‖ ≤ cTK μ * Hh * ‖x - x'‖ ^ μ) := by
  intro d
  intro G gm HolderOnS kw0 kw1 kw2 lap2L Ip ge gK1 gK2 hN wK wK1 wK2 wA Wb FE cTm cH KH1 TK cTK
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_kw1_trans, f_kw2_trans, f_kw3_trans, f_wh_hasDerivAt_kw0_t, f_wh_hasFDerivAt_kw0, f_wh_hasFDerivAt_kw1, f_wh_hasFDerivAt_kw2, f_wh_kw0_le, f_wh_kw0_sub_h, f_wh_kw0_time_diff, f_wh_kw1_hol, f_wh_kw1_le, f_wh_kw1_time_le, f_wh_kw2_hol, f_wh_kw1_lip⟩ := @EthierKurtz.heat_kernel_smoothing_estimates d
  haveI : ObliqueLib.IFacts d := ⟨f_wA_nonneg, f_wh_hasFDerivAt_kw0, f_wh_hasFDerivAt_kw1, f_wh_kw0_sub_h, f_wh_kw0_time_diff, f_wh_kw1_hol, f_wh_kw1_time_le, f_wh_kw2_hol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h μ M Hh hhol hm hμ0 hμ1 e he x x'; exact ObliqueLib.FE_hol hhol hm hμ0 hμ1 he x x'
  · intro μ Hh hH; exact ObliqueLib.KH1_nonneg hH
  · intro h μ M Hh hhol hm hμ0 hμ2 a ha y; exact ObliqueLib.kw2h_tau_le hhol hm hμ0 hμ2 ha y
  · intro h μ M Hh hhol hm hμ0 hμ1 e he x x'; exact ObliqueLib.TK_hol hhol hm hμ0 hμ1 he x x'
