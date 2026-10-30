-- Prove2me | solution 1 for EthierKurtz.ray_integrand_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T13:11:39.482772+00:00
-- url     : https://prove2.me/submissions/2691a0a5-48c9-47be-b3cd-b6a7976ef75c

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_gaussian_fourth_derivative_bound

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

lemma G_pos {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 < G d s z :=
  mul_pos (rpow_pos_of_pos (mul_pos pi_pos hs) _) (exp_pos _)

lemma G_nonneg {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 ≤ G d s z := (G_pos hs z).le

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

section HalfGeom

variable {d : ℕ}

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

noncomputable def wK4 (t : ℝ) (x y : Eu d) :
    Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ := hN d t • gK4 (1 / (2 * t)) (x - y)

end GDeriv4

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  hasFDerivAt_gK1 : ∀ (a : ℝ) (z : Eu d), HasFDerivAt (gK1 a) (gK2 a z) z
  hasFDerivAt_gK2 : ∀ (a : ℝ) (z : Eu d), HasFDerivAt (gK2 a) (gK3 a z) z
  hN_pos : ∀ {t : ℝ} (ht : 0 < t), 0 < hN d t
  wA_nonneg : 0 ≤ wA d
  whole_bounds : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), |wK d t x y| ≤ wA d * G d (4 * t) (x - y) ∧ ‖wK1 t x y‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK2 t x y‖ ≤ wA d * t ^ (-(1 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK3 t x y‖ ≤ wA d * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) (x - y)
  hasFDerivAt_gK3 : ∀ (a : ℝ) (z : Eu d), HasFDerivAt (gK3 a) (gK4 a z) z
  whole_bound4 : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), ‖wK4 t x y‖ ≤ 2 * wA d * t ^ (-(2 : ℝ)) * G d (4 * t) (x - y)

end IFk

export IFacts (hasFDerivAt_gK1 hasFDerivAt_gK2 hN_pos wA_nonneg whole_bounds hasFDerivAt_gK3 whole_bound4)

section GDeriv4b

variable {d : ℕ}

variable [IFacts d]

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

lemma eb1_apply (b : Eu d) (M : Eu d →L[ℝ] ℝ) : eb1 b M = M b := rfl

lemma norm_eb1 (b : Eu d) : ‖eb1 b‖ ≤ ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun M => by
    rw [eb1_apply, mul_comm]; exact M.le_opNorm b

lemma norm_eb2 (b : Eu d) : ‖eb2 b‖ ≤ ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun M =>
    (ContinuousLinearMap.opNorm_comp_le (eb1 b) M).trans
      (mul_le_mul_of_nonneg_right (norm_eb1 b) (norm_nonneg _))

lemma norm_eb3 (b : Eu d) : ‖eb3 b‖ ≤ ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun M =>
    (ContinuousLinearMap.opNorm_comp_le (eb2 b) M).trans
      (mul_le_mul_of_nonneg_right (norm_eb2 b) (norm_nonneg _))

lemma app4_le (M : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (u v z q : Eu d) :
    ‖M u v z q‖ ≤ ‖M‖ * ‖u‖ * ‖v‖ * ‖z‖ * ‖q‖ := by
  calc ‖M u v z q‖ ≤ ‖M u v z‖ * ‖q‖ := (M u v z).le_opNorm q
    _ ≤ ‖M u v‖ * ‖z‖ * ‖q‖ := by gcongr; exact (M u v).le_opNorm z
    _ ≤ ‖M u‖ * ‖v‖ * ‖z‖ * ‖q‖ := by gcongr; exact (M u).le_opNorm v
    _ ≤ ‖M‖ * ‖u‖ * ‖v‖ * ‖z‖ * ‖q‖ := by gcongr; exact M.le_opNorm u

noncomputable def rP0 (b : Eu d) (t : ℝ) (w : Eu d) : ℝ := hN d t * eb1 b (gK1 (1 / (2 * t)) w)

noncomputable def rP1 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] ℝ :=
  hN d t • eb2 b (gK2 (1 / (2 * t)) w)

noncomputable def rP2 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • eb3 b (gK3 (1 / (2 * t)) w)

noncomputable def rP3 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • (eb3 b).comp (gK4 (1 / (2 * t)) w)

lemma rP_d0 (b : Eu d) (t : ℝ) (w : Eu d) : HasFDerivAt (rP0 b t) (rP1 b t w) w := by
  have h := ((eb1 b).hasFDerivAt.comp w (hasFDerivAt_gK1 (d := d) (1 / (2 * t)) w)).const_mul
    (hN d t)
  exact h

lemma rP_d1 (b : Eu d) (t : ℝ) (w : Eu d) : HasFDerivAt (rP1 b t) (rP2 b t w) w := by
  have h := ((eb2 b).hasFDerivAt.comp w (hasFDerivAt_gK2 (d := d) (1 / (2 * t)) w)).const_smul
    (hN d t)
  exact h

lemma rP_d2 (b : Eu d) (t : ℝ) (w : Eu d) : HasFDerivAt (rP2 b t) (rP3 b t w) w := by
  have h := ((eb3 b).hasFDerivAt.comp w (hasFDerivAt_gK3 (d := d) (1 / (2 * t)) w)).const_smul
    (hN d t)
  exact h

lemma rP_bounds (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d) :
    |rP0 b t w| ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) w ∧
    ‖rP1 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 : ℝ)) * G d (4 * t) w ∧
    ‖rP2 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) w ∧
    ‖rP3 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * G d (4 * t) w := by
  obtain ⟨_, b1', b2', b3'⟩ := whole_bounds (d := d) ht w 0
  have b4 := whole_bound4 (d := d) ht w 0
  have hW := wA_nonneg (d := d)
  have hG := G_nonneg (d := d) (by positivity : 0 < 4 * t) (w - 0)
  have b1 := b1'.trans (by gcongr; linarith : wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (w - 0)
    ≤ 2 * wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (w - 0))
  have b2 := b2'.trans (by gcongr; linarith : wA d * t ^ (-(1 : ℝ)) * G d (4 * t) (w - 0)
    ≤ 2 * wA d * t ^ (-(1 : ℝ)) * G d (4 * t) (w - 0))
  have b3 := b3'.trans (by gcongr; linarith : wA d * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) (w - 0)
    ≤ 2 * wA d * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) (w - 0))
  simp only [wK1, wK2, wK3, wK4, sub_zero] at b1 b2 b3 b4
  have hNp := hN_pos (d := d) ht
  have key : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
      [NormedSpace ℝ Y] (L : X →L[ℝ] Y) (M : X) (B : ℝ), ‖L‖ ≤ ‖b‖ → ‖hN d t • M‖ ≤ B →
      ‖hN d t • L M‖ ≤ ‖b‖ * B := by
    intro X Y _ _ _ _ L M B hL hM
    rw [← L.map_smul]
    exact (L.le_opNorm _).trans (mul_le_mul hL hM (norm_nonneg _) (norm_nonneg _))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := key (eb1 b) (gK1 (1 / (2 * t)) w) _ (norm_eb1 b) b1
    rw [rP0, ← smul_eq_mul, ← Real.norm_eq_abs]
    exact this.trans_eq (by ring)
  · exact (key (eb2 b) (gK2 (1 / (2 * t)) w) _ (norm_eb2 b) b2).trans_eq
      (by ring)
  · exact (key (eb3 b) (gK3 (1 / (2 * t)) w) _ (norm_eb3 b) b3).trans_eq
      (by ring)
  · have hB : 0 ≤ ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * G d (4 * t) w :=
      mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg b) (by linarith)) (rpow_nonneg ht.le _))
        (G_nonneg (d := d) (by positivity : (0 : ℝ) < 4 * t) w)
    refine ContinuousLinearMap.opNorm_le_bound _ hB fun u => ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hB (norm_nonneg u)) fun v => ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (mul_nonneg hB (norm_nonneg u)) (norm_nonneg v)) fun z => ?_
    have e : rP3 b t w u v z = (hN d t • gK4 (1 / (2 * t)) w) u v z b := rfl
    rw [e]
    calc ‖(hN d t • gK4 (1 / (2 * t)) w) u v z b‖
        ≤ ‖hN d t • gK4 (1 / (2 * t)) w‖ * ‖u‖ * ‖v‖ * ‖z‖ * ‖b‖ := app4_le _ u v z b
      _ ≤ 2 * wA d * t ^ (-(2 : ℝ)) * G d (4 * t) w * ‖u‖ * ‖v‖ * ‖z‖ * ‖b‖ := by gcongr
      _ = ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * G d (4 * t) w * ‖u‖ * ‖v‖ * ‖z‖ := by ring

end GDeriv4b

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
  let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
  let gK4 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK3 a) z);
  let eb1 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.apply ℝ ℝ b);
  let eb2 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) ℝ (eb1 b));
  let eb3 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (eb2 b));
  let rP0 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t * eb1 b (gK1 (1 / (2 * t)) w));
  let rP1 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb2 b (gK2 (1 / (2 * t)) w));
  let rP2 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb3 b (gK3 (1 / (2 * t)) w));
  let rP3 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • (eb3 b).comp (gK4 (1 / (2 * t)) w));
    (∀ (b : EuclideanSpace ℝ (Fin d)) (M : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ), eb1 b M = M b) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)), HasFDerivAt (rP0 b t) (rP1 b t w) w) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)), HasFDerivAt (rP1 b t) (rP2 b t w) w) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)), HasFDerivAt (rP2 b t) (rP3 b t w) w) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) (w : EuclideanSpace ℝ (Fin d)), |rP0 b t w| ≤ ‖b‖ * (2 * wA) * t ^ (-(1 / 2 : ℝ)) * G (4 * t) w ∧ ‖rP1 b t w‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(1 : ℝ)) * G (4 * t) w ∧ ‖rP2 b t w‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(3 / 2 : ℝ)) * G (4 * t) w ∧ ‖rP3 b t w‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(2 : ℝ)) * G (4 * t) w) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN wA gK4 eb1 eb2 eb3 rP0 rP1 rP2 rP3
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_contDiff_gK3, f_hasFDerivAt_gK3, f_whole_bound4⟩ := @EthierKurtz.gaussian_fourth_derivative_bound d
  haveI : ObliqueLib.IFacts d := ⟨f_hasFDerivAt_gK1, f_hasFDerivAt_gK2, f_hN_pos, f_wA_nonneg, f_whole_bounds, f_hasFDerivAt_gK3, f_whole_bound4⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (fun b M => @ObliqueLib.eb1_apply d _ b M)
  · exact (fun b t w => @ObliqueLib.rP_d0 d _ b t w)
  · exact (fun b t w => @ObliqueLib.rP_d1 d _ b t w)
  · exact (fun b t w => @ObliqueLib.rP_d2 d _ b t w)
  · exact (fun b {t} ht w => @ObliqueLib.rP_bounds d _ b t ht w)
