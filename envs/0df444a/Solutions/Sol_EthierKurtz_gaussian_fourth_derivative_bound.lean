-- Prove2me | solution 1 for EthierKurtz.gaussian_fourth_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T12:41:42.276869+00:00
-- url     : https://prove2.me/submissions/4a2b4267-26de-4d24-acf1-ac71403ea5c4

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus

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

lemma pow_mul_exp_le (k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    a ^ k * rexp (-a) ≤ 2 ^ k * k.factorial * rexp (-a / 2) := by
  have h := Real.pow_div_factorial_le_exp (x := a / 2) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h1 : a ^ k ≤ 2 ^ k * k.factorial * rexp (a / 2) := by
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
    linarith
  calc a ^ k * rexp (-a) ≤ 2 ^ k * k.factorial * rexp (a / 2) * rexp (-a) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = 2 ^ k * k.factorial * rexp (-a / 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- `(|z|^2/s)^k G(s,z) ≤ 2^k k! 2^(d/2) G(2s,z)`. -/
lemma pow_mul_G_le {d : ℕ} (k : ℕ) {s : ℝ} (hs : 0 < s) (z : Eu d) :
    (‖z‖ ^ 2 / s) ^ k * G d s z ≤
      2 ^ k * k.factorial * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z := by
  have hps : 0 < π * s := mul_pos pi_pos hs
  have ha : 0 ≤ ‖z‖ ^ 2 / s := by positivity
  have h := pow_mul_exp_le k ha
  have e1 : (π * (2 * s)) ^ (-((d : ℝ) / 2)) =
      (2 : ℝ) ^ (-((d : ℝ) / 2)) * (π * s) ^ (-((d : ℝ) / 2)) := by
    rw [show π * (2 * s) = 2 * (π * s) by ring, mul_rpow (by norm_num) hps.le]
  have e2 : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-((d : ℝ) / 2)) = 1 := by
    rw [← rpow_add (by norm_num)]; simp
  have e3 : -(‖z‖ ^ 2 / s) / 2 = -‖z‖ ^ 2 / (2 * s) := by field_simp
  unfold G
  rw [e1, ← e3]
  have hP : 0 ≤ (π * s) ^ (-((d : ℝ) / 2)) := (rpow_pos_of_pos hps _).le
  calc (‖z‖ ^ 2 / s) ^ k * ((π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s))
      = (π * s) ^ (-((d : ℝ) / 2)) * ((‖z‖ ^ 2 / s) ^ k * rexp (-(‖z‖ ^ 2 / s))) := by
        rw [neg_div]; ring
    _ ≤ (π * s) ^ (-((d : ℝ) / 2)) * (2 ^ k * k.factorial * rexp (-(‖z‖ ^ 2 / s) / 2)) :=
        mul_le_mul_of_nonneg_left h hP
    _ = 2 ^ k * k.factorial * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-((d : ℝ) / 2))) *
          ((π * s) ^ (-((d : ℝ) / 2)) * rexp (-(‖z‖ ^ 2 / s) / 2)) := by
        rw [e2]; ring
    _ = 2 ^ k * k.factorial * 2 ^ ((d : ℝ) / 2) *
          ((2 : ℝ) ^ (-((d : ℝ) / 2)) * (π * s) ^ (-((d : ℝ) / 2)) *
            rexp (-(‖z‖ ^ 2 / s) / 2)) := by ring

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

section HalfGeom

variable {d : ℕ}

end HalfGeom

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  ge_pos : ∀ (a : ℝ) (z : Eu d), 0 < ge d a z
  gK1_apply : ∀ (a : ℝ) (z v : Eu d), gK1 a z v = -(2 * a) * ge d a z * inner ℝ z v
  hasFDerivAt_ge : ∀ (a : ℝ) (z : Eu d), HasFDerivAt (ge d a) (gK1 a z) z
  contDiff_gK2 : ∀ (a : ℝ), ContDiff ℝ ⊤ (gK2 (d := d) a)
  gK3_apply : ∀ (a : ℝ) (z u v w : Eu d), gK3 a z u v w = ge d a z * (-(8 * a ^ 3) * inner ℝ z u * inner ℝ z v * inner ℝ z w + 4 * a ^ 2 * (inner ℝ z u * inner ℝ v w + inner ℝ u v * inner ℝ z w + inner ℝ z v * inner ℝ u w))
  hN_pos : ∀ {t : ℝ} (ht : 0 < t), 0 < hN d t
  hN_ge : ∀ {t : ℝ} (ht : 0 < t) (z : Eu d), hN d t * ge d (1 / (2 * t)) z = G d (2 * t) z

end IFk

export IFacts (ge_pos gK1_apply hasFDerivAt_ge contDiff_gK2 gK3_apply hN_pos hN_ge)

section GDeriv_dup

variable {d : ℕ}

noncomputable local instance instL2N'_dup (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S'_dup (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable [IFacts d]

lemma abs_mul3_le {p q r P Q R : ℝ} (hp : |p| ≤ P) (hq : |q| ≤ Q) (hr : |r| ≤ R) :
    |p * q * r| ≤ P * Q * R := by
  rw [abs_mul, abs_mul]
  have hP : 0 ≤ P := (abs_nonneg _).trans hp
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hq
  exact mul_le_mul (mul_le_mul hp hq (abs_nonneg _) hP) hr (abs_nonneg _) (mul_nonneg hP hQ)

lemma abs_mul2_le {p q P Q : ℝ} (hp : |p| ≤ P) (hq : |q| ≤ Q) : |p * q| ≤ P * Q := by
  rw [abs_mul]
  exact mul_le_mul hp hq (abs_nonneg _) ((abs_nonneg _).trans hp)

end GDeriv_dup

section Whole_dup

variable {d : ℕ}

noncomputable local instance instL2N5_dup (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S5_dup (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable [IFacts d]

/-- `r = t^(-1/2)` facts. -/
lemma rhalf_facts {t : ℝ} (ht : 0 < t) :
    0 < t ^ (-(1 / 2 : ℝ)) ∧ (t ^ (-(1 / 2 : ℝ))) ^ 2 * t = 1 ∧
      t ^ (-(1 : ℝ)) = (t ^ (-(1 / 2 : ℝ))) ^ 2 ∧ t ^ (-(3 / 2 : ℝ)) = (t ^ (-(1 / 2 : ℝ))) ^ 3 := by
  have e2 : (t ^ (-(1 / 2 : ℝ))) ^ 2 = t ^ (-(1 : ℝ)) := by
    rw [← rpow_natCast, ← rpow_mul ht.le]; norm_num
  have e3 : (t ^ (-(1 / 2 : ℝ))) ^ 3 = t ^ (-(3 / 2 : ℝ)) := by
    rw [← rpow_natCast, ← rpow_mul ht.le]; norm_num
  refine ⟨rpow_pos_of_pos ht _, ?_, e2.symm, e3.symm⟩
  rw [e2, rpow_neg_one, inv_mul_cancel₀ ht.ne']

end Whole_dup

section GDeriv4

variable {d : ℕ}

variable [IFacts d]

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

lemma contDiff_gK3 (a : ℝ) : ContDiff ℝ ⊤ (gK3 (d := d) a) := by
  have : gK3 (d := d) a = fderiv ℝ (gK2 a) := rfl
  rw [this]
  exact (contDiff_gK2 a).fderiv_right le_top

noncomputable def gK4 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  fderiv ℝ (gK3 a) z

lemma hasFDerivAt_gK3 (a : ℝ) (z : Eu d) : HasFDerivAt (gK3 a) (gK4 a z) z :=
  ((contDiff_gK3 a).differentiable (by simp) z).hasFDerivAt

lemma gK4_apply (a : ℝ) (z u v w q : Eu d) :
    gK4 a z u v w q = ge d a z * (16 * a ^ 4 * (inner ℝ z u * inner ℝ z v * inner ℝ z w * inner ℝ z q)
      - 8 * a ^ 3 * (inner ℝ z u * inner ℝ z v * inner ℝ w q + inner ℝ z u * inner ℝ v w * inner ℝ z q
        + inner ℝ z u * inner ℝ z w * inner ℝ v q + inner ℝ u v * inner ℝ z w * inner ℝ z q
        + inner ℝ z v * inner ℝ u w * inner ℝ z q + inner ℝ z v * inner ℝ z w * inner ℝ u q)
      + 4 * a ^ 2 * (inner ℝ u v * inner ℝ w q + inner ℝ v w * inner ℝ u q
        + inner ℝ u w * inner ℝ v q)) := by
  have h1 := (((hasFDerivAt_gK3 a z).clm_apply (hasFDerivAt_const v z)).clm_apply
    (hasFDerivAt_const w z)).clm_apply (hasFDerivAt_const q z)
  have hin : ∀ p : Eu d, HasFDerivAt (fun y : Eu d => inner ℝ y p)
      ((fderivInnerCLM ℝ (z, p)).comp ((ContinuousLinearMap.id ℝ (Eu d)).prod 0)) z :=
    fun p => (hasFDerivAt_id z).inner ℝ (hasFDerivAt_const p z)
  have hv := hin v
  have hw := hin w
  have hq := hin q
  have hcub := ((hv.mul hw).mul hq).const_mul (-(8 * a ^ 3))
  have hlin := (((hv.mul_const (inner ℝ w q)).add (hq.const_mul (inner ℝ v w))).add
    (hw.mul_const (inner ℝ v q))).const_mul (4 * a ^ 2)
  have h2 := (hasFDerivAt_ge (d := d) a z).mul (hcub.add hlin)
  have hfun : (fun y => gK3 a y v w q) = fun y => ge d a y *
      (-(8 * a ^ 3) * (inner ℝ y v * inner ℝ y w * inner ℝ y q) + 4 * a ^ 2 *
        (inner ℝ y v * inner ℝ w q + inner ℝ v w * inner ℝ y q + inner ℝ y w * inner ℝ v q)) := by
    funext y; rw [gK3_apply]; ring
  rw [hfun] at h1
  have := congrArg (fun L => L u) (h1.unique h2)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderivInnerCLM_apply, gK1_apply, inner_zero_right,
    inner_zero_left, add_zero, ContinuousLinearMap.sub_apply, Pi.mul_apply, Pi.add_apply] at this
  rw [this]
  simp only [real_inner_comm u z, real_inner_comm u v, real_inner_comm u w, real_inner_comm u q]
  ring

lemma abs_mul4_le {p q r s P Q R S : ℝ} (hp : |p| ≤ P) (hq : |q| ≤ Q) (hr : |r| ≤ R) (hs : |s| ≤ S) :
    |p * q * r * s| ≤ P * Q * R * S := by
  rw [abs_mul]
  exact mul_le_mul (abs_mul3_le hp hq hr) hs (abs_nonneg _)
    (mul_nonneg (mul_nonneg ((abs_nonneg _).trans hp) ((abs_nonneg _).trans hq))
      ((abs_nonneg _).trans hr))

lemma norm_gK4_le {a : ℝ} (ha : 0 ≤ a) (z : Eu d) :
    ‖gK4 a z‖ ≤ ge d a z * (16 * a ^ 4 * ‖z‖ ^ 4 + 48 * a ^ 3 * ‖z‖ ^ 2 + 12 * a ^ 2) := by
  have hg := ge_pos (d := d) a z
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun w q => ?_
  rw [gK4_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hg]
  set n := ‖z‖
  set K := ‖u‖ * ‖v‖ * ‖w‖ * ‖q‖ with hK
  have iu := abs_real_inner_le_norm z u
  have iv := abs_real_inner_le_norm z v
  have iw := abs_real_inner_le_norm z w
  have iq := abs_real_inner_le_norm z q
  have uv := abs_real_inner_le_norm u v
  have uw := abs_real_inner_le_norm u w
  have uq := abs_real_inner_le_norm u q
  have vw := abs_real_inner_le_norm v w
  have vq := abs_real_inner_le_norm v q
  have wq := abs_real_inner_le_norm w q
  have P4 := abs_le.mp ((abs_mul4_le iu iv iw iq).trans_eq (show n * ‖u‖ * (n * ‖v‖) * (n * ‖w‖)
    * (n * ‖q‖) = n ^ 4 * K by rw [hK]; ring))
  have T1 := abs_le.mp ((abs_mul3_le iu iv wq).trans_eq (show n * ‖u‖ * (n * ‖v‖) * (‖w‖ * ‖q‖)
    = n ^ 2 * K by rw [hK]; ring))
  have T2 := abs_le.mp ((abs_mul3_le iu vw iq).trans_eq (show n * ‖u‖ * (‖v‖ * ‖w‖) * (n * ‖q‖)
    = n ^ 2 * K by rw [hK]; ring))
  have T3 := abs_le.mp ((abs_mul3_le iu iw vq).trans_eq (show n * ‖u‖ * (n * ‖w‖) * (‖v‖ * ‖q‖)
    = n ^ 2 * K by rw [hK]; ring))
  have T4 := abs_le.mp ((abs_mul3_le uv iw iq).trans_eq (show ‖u‖ * ‖v‖ * (n * ‖w‖) * (n * ‖q‖)
    = n ^ 2 * K by rw [hK]; ring))
  have T5 := abs_le.mp ((abs_mul3_le iv uw iq).trans_eq (show n * ‖v‖ * (‖u‖ * ‖w‖) * (n * ‖q‖)
    = n ^ 2 * K by rw [hK]; ring))
  have T6 := abs_le.mp ((abs_mul3_le iv iw uq).trans_eq (show n * ‖v‖ * (n * ‖w‖) * (‖u‖ * ‖q‖)
    = n ^ 2 * K by rw [hK]; ring))
  have R1 := abs_le.mp ((abs_mul2_le uv wq).trans_eq (show ‖u‖ * ‖v‖ * (‖w‖ * ‖q‖) = K by
    rw [hK]; ring))
  have R2 := abs_le.mp ((abs_mul2_le vw uq).trans_eq (show ‖v‖ * ‖w‖ * (‖u‖ * ‖q‖) = K by
    rw [hK]; ring))
  have R3 := abs_le.mp ((abs_mul2_le uw vq).trans_eq (show ‖u‖ * ‖w‖ * (‖v‖ * ‖q‖) = K by
    rw [hK]; ring))
  have a4 : 0 ≤ 16 * a ^ 4 := by positivity
  have a3 : 0 ≤ 8 * a ^ 3 := by positivity
  have a2 : 0 ≤ 4 * a ^ 2 := by positivity
  have key : |16 * a ^ 4 * (inner ℝ z u * inner ℝ z v * inner ℝ z w * inner ℝ z q)
      - 8 * a ^ 3 * (inner ℝ z u * inner ℝ z v * inner ℝ w q + inner ℝ z u * inner ℝ v w * inner ℝ z q
        + inner ℝ z u * inner ℝ z w * inner ℝ v q + inner ℝ u v * inner ℝ z w * inner ℝ z q
        + inner ℝ z v * inner ℝ u w * inner ℝ z q + inner ℝ z v * inner ℝ z w * inner ℝ u q)
      + 4 * a ^ 2 * (inner ℝ u v * inner ℝ w q + inner ℝ v w * inner ℝ u q
        + inner ℝ u w * inner ℝ v q)|
      ≤ (16 * a ^ 4 * n ^ 4 + 48 * a ^ 3 * n ^ 2 + 12 * a ^ 2) * K := by
    rw [abs_le]
    constructor
    · linarith [mul_le_mul_of_nonneg_left P4.1 a4, mul_le_mul_of_nonneg_left T1.2 a3,
        mul_le_mul_of_nonneg_left T2.2 a3, mul_le_mul_of_nonneg_left T3.2 a3,
        mul_le_mul_of_nonneg_left T4.2 a3, mul_le_mul_of_nonneg_left T5.2 a3,
        mul_le_mul_of_nonneg_left T6.2 a3, mul_le_mul_of_nonneg_left R1.1 a2,
        mul_le_mul_of_nonneg_left R2.1 a2, mul_le_mul_of_nonneg_left R3.1 a2]
    · linarith [mul_le_mul_of_nonneg_left P4.2 a4, mul_le_mul_of_nonneg_left T1.1 a3,
        mul_le_mul_of_nonneg_left T2.1 a3, mul_le_mul_of_nonneg_left T3.1 a3,
        mul_le_mul_of_nonneg_left T4.1 a3, mul_le_mul_of_nonneg_left T5.1 a3,
        mul_le_mul_of_nonneg_left T6.1 a3, mul_le_mul_of_nonneg_left R1.2 a2,
        mul_le_mul_of_nonneg_left R2.2 a2, mul_le_mul_of_nonneg_left R3.2 a2]
  calc ge d a z * |_| ≤ ge d a z * ((16 * a ^ 4 * n ^ 4 + 48 * a ^ 3 * n ^ 2 + 12 * a ^ 2) * K) :=
        mul_le_mul_of_nonneg_left key hg.le
    _ = ge d a z * (16 * a ^ 4 * n ^ 4 + 48 * a ^ 3 * n ^ 2 + 12 * a ^ 2) * ‖u‖ * ‖v‖ * ‖w‖ * ‖q‖ := by
        rw [hK]; ring

noncomputable def wK4 (t : ℝ) (x y : Eu d) :
    Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ := hN d t • gK4 (1 / (2 * t)) (x - y)

lemma whole_bound4 {t : ℝ} (ht : 0 < t) (x y : Eu d) :
    ‖wK4 t x y‖ ≤ 2 * wA d * t ^ (-(2 : ℝ)) * G d (4 * t) (x - y) := by
  set z := x - y
  set B : ℝ := 2 ^ ((d : ℝ) / 2) with hB
  obtain ⟨hr, hr2, e1, e3⟩ := rhalf_facts ht
  set r := t ^ (-(1 / 2 : ℝ))
  have e4 : t ^ (-(2 : ℝ)) = r ^ 4 := by
    rw [← rpow_natCast, ← rpow_mul ht.le]; norm_num
  have h44 : G d (2 * (2 * t)) z = G d (4 * t) z := by congr 1; ring
  have p0 := pow_mul_G_le (d := d) 0 (by positivity : 0 < 2 * t) z
  have p1 := pow_mul_G_le (d := d) 1 (by positivity : 0 < 2 * t) z
  have p2 := pow_mul_G_le (d := d) 2 (by positivity : 0 < 2 * t) z
  simp only [pow_zero, one_mul, Nat.factorial, Nat.cast_one, pow_one, h44, Nat.succ_eq_add_one,
    zero_add, mul_one, Nat.cast_ofNat] at p0 p1 p2
  have hg2 := G_nonneg (d := d) (by positivity : 0 < 2 * t) z
  have hti : 1 / t = r ^ 2 := by field_simp; linarith
  set Y := ‖z‖ * r with hY
  have hX : ‖z‖ ^ 2 / (2 * t) = Y ^ 2 / 2 := by rw [hY, mul_pow, ← hti]; field_simp
  rw [hX] at p1 p2
  have ha : (0 : ℝ) ≤ 1 / (2 * t) := by positivity
  have hNp := hN_pos (d := d) ht
  have hNge := hN_ge (d := d) ht z
  have hwA : wA d = 51 * B := rfl
  have e5 : 16 * (1 / (2 * t)) ^ 4 * ‖z‖ ^ 4 + 48 * (1 / (2 * t)) ^ 3 * ‖z‖ ^ 2
      + 12 * (1 / (2 * t)) ^ 2 = r ^ 4 * (Y ^ 4 + 6 * Y ^ 2 + 3) := by
    have : 1 / (2 * t) = r ^ 2 / 2 := by rw [← hti]; field_simp
    rw [this, hY]; ring
  have h4 : Y ^ 4 * G d (2 * t) z ≤ 32 * B * G d (4 * t) z := by
    have : Y ^ 4 = 4 * (Y ^ 2 / 2) ^ 2 := by ring
    rw [this, hB]; linarith
  have q0 : G d (2 * t) z ≤ B * G d (4 * t) z := by rw [hB]; exact p0
  have q1 : Y ^ 2 * G d (2 * t) z ≤ 4 * B * G d (4 * t) z := by rw [hB]; linarith
  have hc : (Y ^ 4 + 6 * Y ^ 2 + 3) * G d (2 * t) z ≤ 102 * B * G d (4 * t) z := by
    linarith
  rw [wK4, norm_smul, Real.norm_eq_abs, abs_of_pos hNp, hwA, e4]
  calc hN d t * ‖gK4 (1 / (2 * t)) z‖ ≤ hN d t * (ge d (1 / (2 * t)) z *
        (16 * (1 / (2 * t)) ^ 4 * ‖z‖ ^ 4 + 48 * (1 / (2 * t)) ^ 3 * ‖z‖ ^ 2
          + 12 * (1 / (2 * t)) ^ 2)) := mul_le_mul_of_nonneg_left (norm_gK4_le ha z) hNp.le
    _ = r ^ 4 * ((Y ^ 4 + 6 * Y ^ 2 + 3) * G d (2 * t) z) := by rw [← hNge, e5]; ring
    _ ≤ r ^ 4 * (102 * B * G d (4 * t) z) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2 * (51 * B) * r ^ 4 * G d (4 * t) z := by ring

end GDeriv4

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
  let gK2 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (ge a z • ((4 * a ^ 2) • (Ip z).smulRight (Ip z) - (2 * a) • Ip));
  let gK3 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK2 a) z);
  let hN : (t : ℝ) → ℝ := fun (t : ℝ) => ((π * (2 * t)) ^ (-((d : ℝ) / 2)));
  let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
  let gK4 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK3 a) z);
  let wK4 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK4 (1 / (2 * t)) (x - y));
    (∀ (a : ℝ), ContDiff ℝ ⊤ (gK3 a)) ∧
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), HasFDerivAt (gK3 a) (gK4 a z) z) ∧
    (∀ {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), ‖wK4 t x y‖ ≤ 2 * wA * t ^ (-(2 : ℝ)) * G (4 * t) (x - y)) := by
  intro d
  intro G Ip ge gK2 gK3 hN wA gK4 wK4
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  haveI : ObliqueLib.IFacts d := ⟨f_ge_pos, f_gK1_apply, f_hasFDerivAt_ge, f_contDiff_gK2, f_gK3_apply, f_hN_pos, f_hN_ge⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (fun a => @ObliqueLib.contDiff_gK3 d _ a)
  · exact (fun a z => @ObliqueLib.hasFDerivAt_gK3 d _ a z)
  · exact (fun {t} ht x y => @ObliqueLib.whole_bound4 d _ t ht x y)
