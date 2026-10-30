-- Prove2me | solution 1 for EthierKurtz.gaussian_heat_kernel_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T12:25:40.64396+00:00
-- url     : https://prove2.me/submissions/a8d7fd4c-7ab6-479e-a5e1-c0c1c201bda8

import Mathlib

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

lemma G_eq {d : ℕ} {s : ℝ} (z : Eu d) :
    G d s z = (π * s) ^ (-((d : ℝ) / 2)) * rexp (-(1 / s) * ‖z‖ ^ 2) := by
  rw [G]; congr 2; ring

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

lemma Ip_apply (v w : Eu d) : Ip d v w = inner ℝ v w := rfl

noncomputable def ge (d : ℕ) (a : ℝ) (z : Eu d) : ℝ := rexp (-(a * ‖z‖ ^ 2))

noncomputable def gK1 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] ℝ := (-(2 * a) * ge d a z) • Ip d z

noncomputable def gK2 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ge d a z • ((4 * a ^ 2) • (Ip d z).smulRight (Ip d z) - (2 * a) • Ip d)

lemma ge_pos (a : ℝ) (z : Eu d) : 0 < ge d a z := exp_pos _

lemma gK1_apply (a : ℝ) (z v : Eu d) : gK1 a z v = -(2 * a) * ge d a z * inner ℝ z v := by
  simp [gK1, Ip_apply]

lemma gK2_apply (a : ℝ) (z v w : Eu d) :
    gK2 a z v w = ge d a z * (4 * a ^ 2 * inner ℝ z v * inner ℝ z w - 2 * a * inner ℝ v w) := by
  simp only [gK2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, Ip_apply, smul_eq_mul]; ring

lemma hasFDerivAt_ge (a : ℝ) (z : Eu d) : HasFDerivAt (ge d a) (gK1 a z) z := by
  have := (((hasFDerivAt_id z).norm_sq).const_mul a).neg.exp
  refine this.congr_fderiv ?_
  ext v; simp [gK1, ge, Ip_apply]; ring

lemma hasFDerivAt_gK1 (a : ℝ) (z : Eu d) : HasFDerivAt (gK1 a) (gK2 a z) z := by
  have hc : HasFDerivAt (fun z => -(2 * a) * ge d a z) ((-(2 * a)) • gK1 a z) z :=
    (hasFDerivAt_ge a z).const_mul _
  have hf : HasFDerivAt (fun z : Eu d => Ip d z) (Ip d) z := (Ip d).hasFDerivAt
  refine (hc.smul hf).congr_fderiv ?_
  ext v w; simp [gK1, gK2, Ip_apply]; ring

lemma contDiff_ge (a : ℝ) : ContDiff ℝ ⊤ (ge d a) := by
  unfold ge
  exact ((contDiff_norm_sq ℝ).const_smul a).neg.exp

lemma contDiff_gK2 (a : ℝ) : ContDiff ℝ ⊤ (gK2 (d := d) a) := by
  have hI : ContDiff ℝ ⊤ (fun z : Eu d => Ip d z) := (Ip d).contDiff
  have hB : ContDiff ℝ ⊤ (fun z : Eu d => (Ip d z).smulRight (Ip d z)) := hI.smulRight hI
  have hM : ContDiff ℝ ⊤ (fun z : Eu d =>
      (4 * a ^ 2) • (Ip d z).smulRight (Ip d z) - (2 * a) • Ip d) :=
    (hB.const_smul _).sub contDiff_const
  exact (contDiff_ge a).smul hM

lemma differentiable_gK2 (a : ℝ) : Differentiable ℝ (gK2 (d := d) a) :=
  (contDiff_gK2 a).differentiable (by simp)

noncomputable def gK3 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  fderiv ℝ (gK2 a) z

lemma hasFDerivAt_gK2 (a : ℝ) (z : Eu d) : HasFDerivAt (gK2 a) (gK3 a z) z :=
  (differentiable_gK2 a z).hasFDerivAt

lemma gK3_apply (a : ℝ) (z u v w : Eu d) :
    gK3 a z u v w = ge d a z * (-(8 * a ^ 3) * inner ℝ z u * inner ℝ z v * inner ℝ z w
      + 4 * a ^ 2 * (inner ℝ z u * inner ℝ v w + inner ℝ u v * inner ℝ z w
        + inner ℝ z v * inner ℝ u w)) := by
  have h1 := ((hasFDerivAt_gK2 a z).clm_apply (hasFDerivAt_const v z)).clm_apply
    (hasFDerivAt_const w z)
  have hv : HasFDerivAt (fun y : Eu d => inner ℝ y v)
      ((fderivInnerCLM ℝ (z, v)).comp ((ContinuousLinearMap.id ℝ (Eu d)).prod 0)) z :=
    (hasFDerivAt_id z).inner ℝ (hasFDerivAt_const v z)
  have hw : HasFDerivAt (fun y : Eu d => inner ℝ y w)
      ((fderivInnerCLM ℝ (z, w)).comp ((ContinuousLinearMap.id ℝ (Eu d)).prod 0)) z :=
    (hasFDerivAt_id z).inner ℝ (hasFDerivAt_const w z)
  have h2 := (hasFDerivAt_ge (d := d) a z).mul (((hv.const_mul (4 * a ^ 2)).mul hw).sub_const
    (2 * a * inner ℝ v w))
  have hfun : (fun y => gK2 a y v w) = fun y => ge d a y * (4 * a ^ 2 * inner ℝ y v * inner ℝ y w
      - 2 * a * inner ℝ v w) := funext fun y => gK2_apply a y v w
  rw [hfun] at h1
  have := congrArg (fun L => L u) (h1.unique h2)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderivInnerCLM_apply, gK1_apply, inner_zero_right,
    inner_zero_left, add_zero, ContinuousLinearMap.sub_apply] at this
  rw [this, Pi.mul_apply]
  simp only [real_inner_comm u z, real_inner_comm u v, real_inner_comm u w]
  ring

lemma abs_mul3_le {p q r P Q R : ℝ} (hp : |p| ≤ P) (hq : |q| ≤ Q) (hr : |r| ≤ R) :
    |p * q * r| ≤ P * Q * R := by
  rw [abs_mul, abs_mul]
  have hP : 0 ≤ P := (abs_nonneg _).trans hp
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hq
  exact mul_le_mul (mul_le_mul hp hq (abs_nonneg _) hP) hr (abs_nonneg _) (mul_nonneg hP hQ)

lemma abs_mul2_le {p q P Q : ℝ} (hp : |p| ≤ P) (hq : |q| ≤ Q) : |p * q| ≤ P * Q := by
  rw [abs_mul]
  exact mul_le_mul hp hq (abs_nonneg _) ((abs_nonneg _).trans hp)

lemma norm_gK1_le {a : ℝ} (ha : 0 ≤ a) (z : Eu d) : ‖gK1 a z‖ ≤ 2 * a * ge d a z * ‖z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := ge_pos (d := d) a z; positivity)
    fun v => ?_
  rw [gK1_apply, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * a),
    abs_of_pos (ge_pos a z), mul_assoc (2 * a * ge d a z)]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z v)
    (by have := ge_pos (d := d) a z; positivity)

lemma norm_gK2_le {a : ℝ} (ha : 0 ≤ a) (z : Eu d) :
    ‖gK2 a z‖ ≤ ge d a z * (4 * a ^ 2 * ‖z‖ ^ 2 + 2 * a) := by
  have hg := ge_pos (d := d) a z
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => ?_
  rw [gK2_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hg]
  have h1 := abs_mul2_le (abs_real_inner_le_norm z v) (abs_real_inner_le_norm z w)
  have h2 := abs_real_inner_le_norm v w
  have : |4 * a ^ 2 * inner ℝ z v * inner ℝ z w - 2 * a * inner ℝ v w|
      ≤ 4 * a ^ 2 * (‖z‖ * ‖v‖ * (‖z‖ * ‖w‖)) + 2 * a * (‖v‖ * ‖w‖) := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [mul_assoc, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * a ^ 2)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * a)]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
  calc ge d a z * |4 * a ^ 2 * inner ℝ z v * inner ℝ z w - 2 * a * inner ℝ v w|
      ≤ ge d a z * (4 * a ^ 2 * (‖z‖ * ‖v‖ * (‖z‖ * ‖w‖)) + 2 * a * (‖v‖ * ‖w‖)) :=
        mul_le_mul_of_nonneg_left this hg.le
    _ = ge d a z * (4 * a ^ 2 * ‖z‖ ^ 2 + 2 * a) * ‖v‖ * ‖w‖ := by ring

lemma norm_gK3_le {a : ℝ} (ha : 0 ≤ a) (z : Eu d) :
    ‖gK3 a z‖ ≤ ge d a z * (8 * a ^ 3 * ‖z‖ ^ 3 + 12 * a ^ 2 * ‖z‖) := by
  have hg := ge_pos (d := d) a z
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => ?_
  rw [gK3_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hg]
  have iu := abs_real_inner_le_norm z u
  have iv := abs_real_inner_le_norm z v
  have iw := abs_real_inner_le_norm z w
  have t1 := abs_mul3_le iu iv iw
  have t2 := abs_mul2_le iu (abs_real_inner_le_norm v w)
  have t3 := abs_mul2_le (abs_real_inner_le_norm u v) iw
  have t4 := abs_mul2_le iv (abs_real_inner_le_norm u w)
  have : |-(8 * a ^ 3) * inner ℝ z u * inner ℝ z v * inner ℝ z w
      + 4 * a ^ 2 * (inner ℝ z u * inner ℝ v w + inner ℝ u v * inner ℝ z w
        + inner ℝ z v * inner ℝ u w)|
      ≤ 8 * a ^ 3 * (‖z‖ * ‖u‖ * (‖z‖ * ‖v‖) * (‖z‖ * ‖w‖)) + 4 * a ^ 2 *
        (‖z‖ * ‖u‖ * (‖v‖ * ‖w‖) + ‖u‖ * ‖v‖ * (‖z‖ * ‖w‖) + ‖z‖ * ‖v‖ * (‖u‖ * ‖w‖)) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [mul_assoc, mul_assoc, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 8 * a ^ 3),
        ← mul_assoc, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_left t1 (by positivity : (0 : ℝ) ≤ 8 * a ^ 3)).trans_eq (by ring)
    · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * a ^ 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add t2 t3)) t4)
  calc ge d a z * |_| ≤ ge d a z * (8 * a ^ 3 * (‖z‖ * ‖u‖ * (‖z‖ * ‖v‖) * (‖z‖ * ‖w‖)) + 4 * a ^ 2 *
        (‖z‖ * ‖u‖ * (‖v‖ * ‖w‖) + ‖u‖ * ‖v‖ * (‖z‖ * ‖w‖) + ‖z‖ * ‖v‖ * (‖u‖ * ‖w‖))) :=
        mul_le_mul_of_nonneg_left this hg.le
    _ = ge d a z * (8 * a ^ 3 * ‖z‖ ^ 3 + 12 * a ^ 2 * ‖z‖) * ‖u‖ * ‖v‖ * ‖w‖ := by ring

end GDeriv

section Whole

variable {d : ℕ}

noncomputable local instance instL2N5 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S5 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Normalisation of the heat kernel at time `t`. -/
noncomputable def hN (d : ℕ) (t : ℝ) : ℝ := (π * (2 * t)) ^ (-((d : ℝ) / 2))

lemma G_eq_ge (s : ℝ) (z : Eu d) : G d s z = (π * s) ^ (-((d : ℝ) / 2)) * ge d (1 / s) z := by
  rw [G_eq, ge]; congr 2; ring

noncomputable def wK (d : ℕ) (t : ℝ) (x y : Eu d) : ℝ := G d (2 * t) (x - y)

noncomputable def wK1 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] ℝ := hN d t • gK1 (1 / (2 * t)) (x - y)

noncomputable def wK2 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • gK2 (1 / (2 * t)) (x - y)

noncomputable def wK3 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • gK3 (1 / (2 * t)) (x - y)

lemma hasFDerivAt_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Eu d → F}
    {f' : Eu d → (Eu d →L[ℝ] F)} (hf : ∀ z, HasFDerivAt f (f' z) z) (c : ℝ) (x y : Eu d) :
    HasFDerivAt (fun x => c • f (x - y)) (c • f' (x - y)) x := by
  have h := ((hf (x - y)).comp x ((hasFDerivAt_id x).sub_const y)).const_smul c
  rw [ContinuousLinearMap.comp_id] at h
  exact h

lemma wK_d1 (t : ℝ) (x y : Eu d) : HasFDerivAt (fun x => wK d t x y) (wK1 t x y) x := by
  have := hasFDerivAt_shift (hasFDerivAt_ge (d := d) (1 / (2 * t))) (hN d t) x y
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun x' => ?_)
  simp only [wK, smul_eq_mul, G_eq_ge, hN]

lemma wK_d2 (t : ℝ) (x y : Eu d) : HasFDerivAt (fun x => wK1 t x y) (wK2 t x y) x :=
  hasFDerivAt_shift (hasFDerivAt_gK1 (d := d) (1 / (2 * t))) (hN d t) x y

lemma wK_d3 (t : ℝ) (x y : Eu d) : HasFDerivAt (fun x => wK2 t x y) (wK3 t x y) x :=
  hasFDerivAt_shift (hasFDerivAt_gK2 (d := d) (1 / (2 * t))) (hN d t) x y

lemma hN_pos {t : ℝ} (ht : 0 < t) : 0 < hN d t := rpow_pos_of_pos (by positivity) _

lemma hN_ge {t : ℝ} (ht : 0 < t) (z : Eu d) : hN d t * ge d (1 / (2 * t)) z = G d (2 * t) z := by
  rw [G_eq_ge, hN]

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

/-- Scalar core of the Gaussian derivative bounds. -/
lemma whole_core {n g2 g4 B r t : ℝ} (ht : 0 < t) (hr : 0 < r) (hr2 : r ^ 2 * t = 1)
    (hn : 0 ≤ n) (hg2 : 0 ≤ g2) (h0 : g2 ≤ B * g4) (h1 : n ^ 2 / (2 * t) * g2 ≤ 2 * B * g4)
    (h2 : (n ^ 2 / (2 * t)) ^ 2 * g2 ≤ 8 * B * g4) :
    g2 * (2 * (1 / (2 * t)) * n) ≤ 5 * B * r * g4 ∧
      g2 * (4 * (1 / (2 * t)) ^ 2 * n ^ 2 + 2 * (1 / (2 * t))) ≤ 5 * B * r ^ 2 * g4 ∧
      g2 * (8 * (1 / (2 * t)) ^ 3 * n ^ 3 + 12 * (1 / (2 * t)) ^ 2 * n) ≤ 51 * B * r ^ 3 * g4 := by
  have hti : 1 / t = r ^ 2 := by field_simp; linarith
  set Y := n * r with hY
  have hX : n ^ 2 / (2 * t) = Y ^ 2 / 2 := by
    rw [hY, mul_pow, ← hti]; field_simp
  rw [hX] at h1 h2
  have hY0 : 0 ≤ Y := mul_nonneg hn hr.le
  have hYg : Y * g2 ≤ g2 + Y ^ 2 * g2 := by
    linarith [mul_nonneg hg2 (sq_nonneg (Y - 1)), mul_nonneg hg2 hY0]
  have hY3 : Y ^ 3 * g2 ≤ Y ^ 2 * g2 + Y ^ 4 * g2 := by
    have hq := mul_nonneg hg2 (sq_nonneg Y)
    linarith [mul_nonneg hq (sq_nonneg (Y - 1)), mul_nonneg hq hY0]
  have e1 : 2 * (1 / (2 * t)) * n = r * Y := by
    rw [hY, show 2 * (1 / (2 * t)) = 1 / t by field_simp, hti]; ring
  have e2 : 4 * (1 / (2 * t)) ^ 2 * n ^ 2 + 2 * (1 / (2 * t)) = r ^ 2 * (Y ^ 2 + 1) := by
    have : 1 / (2 * t) = r ^ 2 / 2 := by rw [← hti]; field_simp
    rw [this, hY]; ring
  have e3 : 8 * (1 / (2 * t)) ^ 3 * n ^ 3 + 12 * (1 / (2 * t)) ^ 2 * n = r ^ 3 * (Y ^ 3 + 3 * Y) := by
    have : 1 / (2 * t) = r ^ 2 / 2 := by rw [← hti]; field_simp
    rw [this, hY]; ring
  have hB4 : 0 ≤ B * g4 := hg2.trans h0
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    have : Y * g2 ≤ 5 * B * g4 := by linarith
    calc g2 * (r * Y) = r * (Y * g2) := by ring
      _ ≤ r * (5 * B * g4) := mul_le_mul_of_nonneg_left this hr.le
      _ = 5 * B * r * g4 := by ring
  · rw [e2]
    have : (Y ^ 2 + 1) * g2 ≤ 5 * B * g4 := by linarith
    calc g2 * (r ^ 2 * (Y ^ 2 + 1)) = r ^ 2 * ((Y ^ 2 + 1) * g2) := by ring
      _ ≤ r ^ 2 * (5 * B * g4) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 5 * B * r ^ 2 * g4 := by ring
  · rw [e3]
    have h4 : Y ^ 4 * g2 ≤ 32 * B * g4 := by
      linarith
    have : (Y ^ 3 + 3 * Y) * g2 ≤ 51 * B * g4 := by linarith
    calc g2 * (r ^ 3 * (Y ^ 3 + 3 * Y)) = r ^ 3 * ((Y ^ 3 + 3 * Y) * g2) := by ring
      _ ≤ r ^ 3 * (51 * B * g4) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 51 * B * r ^ 3 * g4 := by ring

/-- The constant of the whole-space kernel bounds. -/
noncomputable def wA (d : ℕ) : ℝ := 51 * 2 ^ ((d : ℝ) / 2)

lemma wA_nonneg : 0 ≤ wA d := by unfold wA; positivity

lemma whole_bounds {t : ℝ} (ht : 0 < t) (x y : Eu d) :
    |wK d t x y| ≤ wA d * G d (4 * t) (x - y) ∧
    ‖wK1 t x y‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - y) ∧
    ‖wK2 t x y‖ ≤ wA d * t ^ (-(1 : ℝ)) * G d (4 * t) (x - y) ∧
    ‖wK3 t x y‖ ≤ wA d * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) (x - y) := by
  set z := x - y
  set B : ℝ := 2 ^ ((d : ℝ) / 2) with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨hr, hr2, e1, e3⟩ := rhalf_facts ht
  set r := t ^ (-(1 / 2 : ℝ))
  have h44 : G d (2 * (2 * t)) z = G d (4 * t) z := by congr 1; ring
  have p0 := pow_mul_G_le (d := d) 0 (by positivity : 0 < 2 * t) z
  have p1 := pow_mul_G_le (d := d) 1 (by positivity : 0 < 2 * t) z
  have p2 := pow_mul_G_le (d := d) 2 (by positivity : 0 < 2 * t) z
  simp only [pow_zero, one_mul, Nat.factorial, Nat.cast_one, pow_one, h44, Nat.succ_eq_add_one,
    zero_add, mul_one, Nat.cast_ofNat] at p0 p1 p2
  have hg2 := G_nonneg (d := d) (by positivity : 0 < 2 * t) z
  have hg4 := G_nonneg (d := d) (by positivity : 0 < 4 * t) z
  obtain ⟨c1, c2, c3⟩ := whole_core (n := ‖z‖) (g2 := G d (2 * t) z) (g4 := G d (4 * t) z) (B := B)
    ht hr hr2 (norm_nonneg _) hg2 p0 (by linarith) (by linarith)
  have ha : (0 : ℝ) ≤ 1 / (2 * t) := by positivity
  have hNp := hN_pos (d := d) ht
  have hNge := hN_ge (d := d) ht z
  have hwA : wA d = 51 * B := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hB4 : G d (2 * t) z ≤ B * G d (4 * t) z := p0
    rw [wK, abs_of_nonneg hg2, hwA]; linarith [mul_nonneg hB0 hg4]
  · rw [wK1, norm_smul, Real.norm_eq_abs, abs_of_pos hNp, hwA]
    calc hN d t * ‖gK1 (1 / (2 * t)) z‖ ≤ hN d t * (2 * (1 / (2 * t)) * ge d (1 / (2 * t)) z * ‖z‖) :=
          mul_le_mul_of_nonneg_left (norm_gK1_le ha z) hNp.le
      _ = G d (2 * t) z * (2 * (1 / (2 * t)) * ‖z‖) := by rw [← hNge]; ring
      _ ≤ 5 * B * r * G d (4 * t) z := c1
      _ ≤ 51 * B * r * G d (4 * t) z := by gcongr; norm_num
  · rw [wK2, norm_smul, Real.norm_eq_abs, abs_of_pos hNp, hwA, e1]
    calc hN d t * ‖gK2 (1 / (2 * t)) z‖ ≤ hN d t * (ge d (1 / (2 * t)) z *
          (4 * (1 / (2 * t)) ^ 2 * ‖z‖ ^ 2 + 2 * (1 / (2 * t)))) :=
          mul_le_mul_of_nonneg_left (norm_gK2_le ha z) hNp.le
      _ = G d (2 * t) z * (4 * (1 / (2 * t)) ^ 2 * ‖z‖ ^ 2 + 2 * (1 / (2 * t))) := by
          rw [← hNge]; ring
      _ ≤ 5 * B * r ^ 2 * G d (4 * t) z := c2
      _ ≤ 51 * B * r ^ 2 * G d (4 * t) z := by gcongr; norm_num
  · rw [wK3, norm_smul, Real.norm_eq_abs, abs_of_pos hNp, hwA, e3]
    calc hN d t * ‖gK3 (1 / (2 * t)) z‖ ≤ hN d t * (ge d (1 / (2 * t)) z *
          (8 * (1 / (2 * t)) ^ 3 * ‖z‖ ^ 3 + 12 * (1 / (2 * t)) ^ 2 * ‖z‖)) :=
          mul_le_mul_of_nonneg_left (norm_gK3_le ha z) hNp.le
      _ = G d (2 * t) z * (8 * (1 / (2 * t)) ^ 3 * ‖z‖ ^ 3 + 12 * (1 / (2 * t)) ^ 2 * ‖z‖) := by
          rw [← hNge]; ring
      _ ≤ 51 * B * r ^ 3 * G d (4 * t) z := c3

end Whole

section HalfGeom

variable {d : ℕ}

/-- Reflection across the hyperplane `⟪x, e⟫ = 0`. -/
noncomputable def Rf (e x : Eu d) : Eu d := x - (2 * inner ℝ x e) • e

lemma inner_self_unit {e : Eu d} (he : ‖e‖ = 1) : inner ℝ e e = (1 : ℝ) := by
  rw [real_inner_self_eq_norm_sq, he]; norm_num

lemma inner_Rf {e : Eu d} (he : ‖e‖ = 1) (x : Eu d) : inner ℝ (Rf e x) e = -inner ℝ x e := by
  simp only [Rf, inner_sub_left, real_inner_smul_left, inner_self_unit he]; ring

lemma norm_sub_Rf_sq {e : Eu d} (he : ‖e‖ = 1) (x y : Eu d) :
    ‖x - Rf e y‖ ^ 2 = ‖x - y‖ ^ 2 + 4 * inner ℝ x e * inner ℝ y e := by
  have h : x - Rf e y = (x - y) + (2 * inner ℝ y e) • e := by
    simp only [Rf]; abel
  rw [h, norm_add_sq_real, norm_smul, real_inner_smul_right, inner_sub_left, he,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma G_le_of_norm_le {s : ℝ} (hs : 0 < s) {z z' : Eu d} (h : ‖z'‖ ≤ ‖z‖) :
    G d s z ≤ G d s z' := by
  unfold G
  refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity)
  have : ‖z'‖ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [div_le_div_iff_of_pos_right hs]; linarith

lemma G_Rf_le {e : Eu d} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) {x y : Eu d}
    (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e) : G d s (x - Rf e y) ≤ G d s (x - y) := by
  refine G_le_of_norm_le hs ?_
  have h := norm_sub_Rf_sq he x y
  have h4 : 0 ≤ 4 * inner ℝ x e * inner ℝ y e := by positivity
  have hsq : ‖x - y‖ ^ 2 ≤ ‖x - Rf e y‖ ^ 2 := by linarith
  nlinarith [norm_nonneg (x - y), norm_nonneg (x - Rf e y)]

lemma rpow_scale {σ K p : ℝ} (hσ : 0 < σ) (hK : 0 < K) :
    (π * σ) ^ (-p) = K ^ p * (π * (K * σ)) ^ (-p) := by
  rw [show π * (K * σ) = K * (π * σ) by ring, mul_rpow hK.le (by positivity), ← mul_assoc,
    ← rpow_add hK]
  simp

/-- Changing the variance parameter of `G`. -/
lemma G_mono_s {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') (z : Eu d) :
    G d s z ≤ (s' / s) ^ ((d : ℝ) / 2) * G d s' z := by
  have hs' : 0 < s' := hs.trans_le hss
  have hK : 0 < s' / s := div_pos hs' hs
  unfold G
  rw [rpow_scale (K := s' / s) hs hK, show s' / s * s = s' by field_simp, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_)
    (by positivity)) (by positivity)
  rw [div_le_div_iff₀ hs hs']
  nlinarith [sq_nonneg ‖z‖]

/-- The constant of the ray lower bound. -/
noncomputable def rK (b : Eu d) : ℝ := 14 + 8 * ‖b‖ ^ 2

lemma one_le_rK (b : Eu d) : 1 ≤ rK b := by unfold rK; nlinarith [sq_nonneg ‖b‖]

lemma rK_pos (b : Eu d) : 0 < rK b := lt_of_lt_of_le one_pos (one_le_rK b)

/-- Ray lower bound: for `⟪z, e⟫ ≥ -m` and `s ≥ 0`. -/
lemma ray_lower {e b z : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m s : ℝ} (hm : 0 ≤ m)
    (hz : -m ≤ inner ℝ z e) (hs : 0 ≤ s) :
    ‖z‖ ^ 2 + s ^ 2 ≤ rK b * ‖z + s • (e - b)‖ ^ 2 + rK b * m ^ 2 := by
  set p := inner ℝ z e with hp
  set w := z - p • e - s • b with hw
  have hee := inner_self_unit he
  have hwe : inner ℝ w e = (0 : ℝ) := by
    simp only [hw, inner_sub_left, real_inner_smul_left, hee, hb]; ring
  have hew : inner ℝ e w = (0 : ℝ) := by rw [real_inner_comm]; exact hwe
  have h1 : z + s • (e - b) = (p + s) • e + w := by
    simp only [hw, smul_sub, add_smul]; abel
  have h2 : z = p • e + (w + s • b) := by simp only [hw]; abel
  have hN1 : ‖z + s • (e - b)‖ ^ 2 = (p + s) ^ 2 + ‖w‖ ^ 2 := by
    rw [h1, norm_add_sq_real, norm_smul, real_inner_smul_left, hew, he, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hebs : inner ℝ e (w + s • b) = (0 : ℝ) := by
    rw [inner_add_right, hew, real_inner_smul_right, real_inner_comm, hb]; ring
  have hN2 : ‖z‖ ^ 2 = p ^ 2 + ‖w + s • b‖ ^ 2 := by
    conv_lhs => rw [h2]
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left, hebs, he, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hN3 : ‖w + s • b‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 + 2 * (s ^ 2 * ‖b‖ ^ 2) := by
    have ht := norm_add_le w (s • b)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] at ht
    have h0 := norm_nonneg (w + s • b)
    have h4 : ‖w + s • b‖ ^ 2 ≤ (‖w‖ + s * ‖b‖) ^ 2 := pow_le_pow_left₀ h0 ht 2
    linarith [sq_nonneg (‖w‖ - s * ‖b‖)]
  set B := ‖b‖ ^ 2
  set W := ‖w‖ ^ 2
  have hB : 0 ≤ B := sq_nonneg _
  have hW : 0 ≤ W := sq_nonneg _
  rw [hN1, hN2]
  unfold rK
  have hBs : 0 ≤ B * (p + s) ^ 2 := mul_nonneg hB (sq_nonneg _)
  have hBW : 0 ≤ B * W := mul_nonneg hB hW
  have hBm : 0 ≤ B * m ^ 2 := mul_nonneg hB (sq_nonneg _)
  rcases le_or_gt 0 p with hp0 | hp0
  · have hps : 0 ≤ p * s := mul_nonneg hp0 hs
    have e1 : p ^ 2 + s ^ 2 ≤ (p + s) ^ 2 := by linarith
    have e2 : B * s ^ 2 ≤ B * (p + s) ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith [sq_nonneg p]) hB
    linarith [sq_nonneg (p + s), sq_nonneg m]
  · have e0 : 0 ≤ (m - p) * (m + p) := mul_nonneg (by linarith) (by linarith)
    have e1 : p ^ 2 ≤ m ^ 2 := by linarith
    have e2 : s ^ 2 ≤ 2 * (p + s) ^ 2 + 2 * m ^ 2 := by linarith [sq_nonneg (2 * p + s), e1]
    have e3 : B * s ^ 2 ≤ B * (2 * (p + s) ^ 2 + 2 * m ^ 2) := mul_le_mul_of_nonneg_left e2 hB
    linarith [sq_nonneg (p + s), sq_nonneg m]

/-- Pointwise Gaussian bound along the ray. -/
lemma G_ray_le {e b z : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m s σ : ℝ} (hm : 0 ≤ m)
    (hz : -m ≤ inner ℝ z e) (hs : 0 ≤ s) (hσ : 0 < σ) :
    G d σ (z + s • (e - b)) ≤ rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z *
      rexp (-(1 / (rK b * σ)) * s ^ 2) := by
  have hK := rK_pos b
  have hl := ray_lower (d := d) he hb hm hz hs
  unfold G
  rw [rpow_scale (K := rK b) hσ hK]
  have hE : -‖z + s • (e - b)‖ ^ 2 / σ ≤
      m ^ 2 / σ + (-‖z‖ ^ 2 / (rK b * σ)) + (-(1 / (rK b * σ)) * s ^ 2) := by
    have hKσ : 0 < rK b * σ := mul_pos hK hσ
    have hK0 : rK b ≠ 0 := hK.ne'
    have hσ0 : σ ≠ 0 := hσ.ne'
    have hdiff : (m ^ 2 / σ + (-‖z‖ ^ 2 / (rK b * σ)) + (-(1 / (rK b * σ)) * s ^ 2))
        - (-‖z + s • (e - b)‖ ^ 2 / σ)
        = (rK b * ‖z + s • (e - b)‖ ^ 2 + rK b * m ^ 2 - ‖z‖ ^ 2 - s ^ 2) / (rK b * σ) := by
      field_simp; ring
    have : 0 ≤ (rK b * ‖z + s • (e - b)‖ ^ 2 + rK b * m ^ 2 - ‖z‖ ^ 2 - s ^ 2) / (rK b * σ) :=
      div_nonneg (by linarith) hKσ.le
    linarith
  calc rK b ^ ((d : ℝ) / 2) * (π * (rK b * σ)) ^ (-((d : ℝ) / 2)) *
        rexp (-‖z + s • (e - b)‖ ^ 2 / σ)
      ≤ rK b ^ ((d : ℝ) / 2) * (π * (rK b * σ)) ^ (-((d : ℝ) / 2)) *
        rexp (m ^ 2 / σ + (-‖z‖ ^ 2 / (rK b * σ)) + (-(1 / (rK b * σ)) * s ^ 2)) := by
        gcongr
    _ = _ := by rw [exp_add, exp_add]; ring

/-- The constant of the ray integral. -/
noncomputable def rC (d : ℕ) (b : Eu d) (m σ : ℝ) : ℝ :=
  rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * (√(π * (rK b * σ)) / 2)

lemma rC_nonneg (b : Eu d) (m σ : ℝ) : 0 ≤ rC d b m σ := by
  have := rK_pos b; unfold rC; positivity

end HalfGeom

end ObliqueLib

open ObliqueLib in
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
  let rC : (b : EuclideanSpace ℝ (Fin d)) → (m σ : ℝ) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (m σ : ℝ) => (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * (√(π * (rK b * σ)) / 2));
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), 0 < ge a z) ∧
    (∀ (a : ℝ) (z v : EuclideanSpace ℝ (Fin d)), gK1 a z v = -(2 * a) * ge a z * inner ℝ z v) ∧
    (∀ (a : ℝ) (z v w : EuclideanSpace ℝ (Fin d)), gK2 a z v w = ge a z * (4 * a ^ 2 * inner ℝ z v * inner ℝ z w - 2 * a * inner ℝ v w)) ∧
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), HasFDerivAt (ge a) (gK1 a z) z) ∧
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), HasFDerivAt (gK1 a) (gK2 a z) z) ∧
    (∀ (a : ℝ), ContDiff ℝ ⊤ (gK2 a)) ∧
    (∀ (a : ℝ) (z : EuclideanSpace ℝ (Fin d)), HasFDerivAt (gK2 a) (gK3 a z) z) ∧
    (∀ (a : ℝ) (z u v w : EuclideanSpace ℝ (Fin d)), gK3 a z u v w = ge a z * (-(8 * a ^ 3) * inner ℝ z u * inner ℝ z v * inner ℝ z w + 4 * a ^ 2 * (inner ℝ z u * inner ℝ v w + inner ℝ u v * inner ℝ z w + inner ℝ z v * inner ℝ u w))) ∧
    (∀ (s : ℝ) (z : EuclideanSpace ℝ (Fin d)), G s z = (π * s) ^ (-((d : ℝ) / 2)) * ge (1 / s) z) ∧
    (∀ (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => wK t x y) (wK1 t x y) x) ∧
    (∀ (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => wK1 t x y) (wK2 t x y) x) ∧
    (∀ (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => wK2 t x y) (wK3 t x y) x) ∧
    (∀ {t : ℝ} (ht : 0 < t), 0 < hN t) ∧
    (∀ {t : ℝ} (ht : 0 < t) (z : EuclideanSpace ℝ (Fin d)), hN t * ge (1 / (2 * t)) z = G (2 * t) z) ∧
    (0 ≤ wA) ∧
    (∀ {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), |wK t x y| ≤ wA * G (4 * t) (x - y) ∧ ‖wK1 t x y‖ ≤ wA * t ^ (-(1 / 2 : ℝ)) * G (4 * t) (x - y) ∧ ‖wK2 t x y‖ ≤ wA * t ^ (-(1 : ℝ)) * G (4 * t) (x - y) ∧ ‖wK3 t x y‖ ≤ wA * t ^ (-(3 / 2 : ℝ)) * G (4 * t) (x - y)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1), inner ℝ e e = (1 : ℝ)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x : EuclideanSpace ℝ (Fin d)), inner ℝ (Rf e x) e = -inner ℝ x e) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (x y : EuclideanSpace ℝ (Fin d)), ‖x - Rf e y‖ ^ 2 = ‖x - y‖ ^ 2 + 4 * inner ℝ x e * inner ℝ y e) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) {x y : EuclideanSpace ℝ (Fin d)} (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e), G s (x - Rf e y) ≤ G s (x - y)) ∧
    (∀ {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') (z : EuclideanSpace ℝ (Fin d)), G s z ≤ (s' / s) ^ ((d : ℝ) / 2) * G s' z) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)), 1 ≤ rK b) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)), 0 < rK b) ∧
    (∀ {e b z : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m s σ : ℝ} (hm : 0 ≤ m) (hz : -m ≤ inner ℝ z e) (hs : 0 ≤ s) (hσ : 0 < σ), G σ (z + s • (e - b)) ≤ rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G (rK b * σ) z * rexp (-(1 / (rK b * σ)) * s ^ 2)) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) (m σ : ℝ), 0 ≤ rC b m σ) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN wK wK1 wK2 wK3 wA Rf rK rC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fun a z => @ObliqueLib.ge_pos d a z)
  · exact (fun a z v => @ObliqueLib.gK1_apply d a z v)
  · exact (fun a z v w => @ObliqueLib.gK2_apply d a z v w)
  · exact (fun a z => @ObliqueLib.hasFDerivAt_ge d a z)
  · exact (fun a z => @ObliqueLib.hasFDerivAt_gK1 d a z)
  · exact (fun a => @ObliqueLib.contDiff_gK2 d a)
  · exact (fun a z => @ObliqueLib.hasFDerivAt_gK2 d a z)
  · exact (fun a z u v w => @ObliqueLib.gK3_apply d a z u v w)
  · exact (fun s z => @ObliqueLib.G_eq_ge d s z)
  · exact (fun t x y => @ObliqueLib.wK_d1 d t x y)
  · exact (fun t x y => @ObliqueLib.wK_d2 d t x y)
  · exact (fun t x y => @ObliqueLib.wK_d3 d t x y)
  · exact (fun {t} ht => @ObliqueLib.hN_pos d t ht)
  · exact (fun {t} ht z => @ObliqueLib.hN_ge d t ht z)
  · exact @ObliqueLib.wA_nonneg d
  · exact (fun {t} ht x y => @ObliqueLib.whole_bounds d t ht x y)
  · exact (fun {e} he => @ObliqueLib.inner_self_unit d e he)
  · exact (fun {e} he x => @ObliqueLib.inner_Rf d e he x)
  · exact (fun {e} he x y => @ObliqueLib.norm_sub_Rf_sq d e he x y)
  · exact (fun {e} he {s} hs {x y} hx hy => @ObliqueLib.G_Rf_le d e he s hs x y hx hy)
  · exact (fun {s s'} hs hss z => @ObliqueLib.G_mono_s d s s' hs hss z)
  · exact (fun b => @ObliqueLib.one_le_rK d b)
  · exact (fun b => @ObliqueLib.rK_pos d b)
  · exact (fun {e b z} he hb {m s σ} hm hz hs hσ => @ObliqueLib.G_ray_le d e b z he hb m s σ hm hz hs hσ)
  · exact (fun b m σ => @ObliqueLib.rC_nonneg d b m σ)
