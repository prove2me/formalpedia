-- Prove2me | solution 1 for EthierKurtz.oblique_kernel_schauder_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T22:15:54.404984+00:00
-- url     : https://prove2.me/submissions/e20734dd-f841-4602-b2e6-c0b9611d5528

import Mathlib

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

lemma integral_exp_sq {d : ℕ} {b : ℝ} (hb : 0 < b) :
    ∫ v : Eu d, rexp (-b * ‖v‖ ^ 2) = (π / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

lemma G_pos {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 < G d s z :=
  mul_pos (rpow_pos_of_pos (mul_pos pi_pos hs) _) (exp_pos _)

lemma G_nonneg {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 ≤ G d s z := (G_pos hs z).le

lemma G_eq {d : ℕ} {s : ℝ} (z : Eu d) :
    G d s z = (π * s) ^ (-((d : ℝ) / 2)) * rexp (-(1 / s) * ‖z‖ ^ 2) := by
  rw [G]; congr 2; ring

lemma continuous_G {d : ℕ} (s : ℝ) : Continuous (G d s) := by
  unfold G; fun_prop

lemma integrable_G {d : ℕ} {s : ℝ} (hs : 0 < s) : Integrable (G d s) := by
  have h := (integrable_exp_sq (d := d) (b := 1 / s) (by positivity)).const_mul
    ((π * s) ^ (-((d : ℝ) / 2)))
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  rw [G_eq]

lemma integral_G {d : ℕ} {s : ℝ} (hs : 0 < s) : ∫ z, G d s z = 1 := by
  simp_rw [G_eq]
  rw [integral_const_mul, integral_exp_sq (by positivity)]
  have hps : 0 < π * s := mul_pos pi_pos hs
  rw [show π / (1 / s) = π * s by field_simp, rpow_neg hps.le]
  exact inv_mul_cancel₀ (rpow_pos_of_pos hps _).ne'

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

/-- `|z|^μ ≤ s^(μ/2) (1 + |z|^2/s)` for `0 ≤ μ ≤ 2`. -/
lemma rpow_norm_le {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (z : Eu d) :
    ‖z‖ ^ μ ≤ s ^ (μ / 2) * (1 + ‖z‖ ^ 2 / s) := by
  set a := ‖z‖ ^ 2 / s with ha_def
  have ha : 0 ≤ a := by positivity
  have hz : ‖z‖ ^ μ = s ^ (μ / 2) * a ^ (μ / 2) := by
    rw [ha_def, div_rpow (by positivity) hs.le, ← rpow_natCast, ← rpow_mul (norm_nonneg _)]
    rw [mul_div_cancel₀ _ (rpow_pos_of_pos hs _).ne']
    congr 1; push_cast; ring
  rw [hz]
  refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg hs.le _)
  rcases le_total a 1 with h1 | h1
  · have := rpow_le_one ha h1 (by linarith : 0 ≤ μ / 2)
    linarith
  · have := rpow_le_rpow_of_exponent_le h1 (by linarith : μ / 2 ≤ 1)
    rw [rpow_one] at this
    linarith

/-- Gaussian moment constant. -/
noncomputable def gm (d : ℕ) : ℝ := 1 + 2 * 2 ^ ((d : ℝ) / 2)

lemma gm_pos (d : ℕ) : 0 < gm d := by unfold gm; positivity

lemma moment_bound_pt {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (z : Eu d) :
    G d s z * ‖z‖ ^ μ ≤ s ^ (μ / 2) * (G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z) := by
  have h1 := rpow_norm_le hs hμ0 hμ2 z
  have h2 := pow_mul_G_le 1 hs z
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h2
  have hG := G_nonneg hs z
  have hsμ : 0 ≤ s ^ (μ / 2) := rpow_nonneg hs.le _
  calc G d s z * ‖z‖ ^ μ ≤ G d s z * (s ^ (μ / 2) * (1 + ‖z‖ ^ 2 / s)) :=
        mul_le_mul_of_nonneg_left h1 hG
    _ = s ^ (μ / 2) * (G d s z + ‖z‖ ^ 2 / s * G d s z) := by ring
    _ ≤ s ^ (μ / 2) * (G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z) := by
        gcongr

lemma integrable_G_mul_rpow {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) :
    Integrable (fun z : Eu d => G d s z * ‖z‖ ^ μ) := by
  have hI : Integrable (fun z : Eu d =>
      s ^ (μ / 2) * (G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z)) :=
    ((integrable_G hs).add ((integrable_G (by positivity)).const_mul _)).const_mul _
  refine hI.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((continuous_G s).mul (continuous_norm.rpow_const fun _ => Or.inr hμ0)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (G_nonneg hs z) (rpow_nonneg (norm_nonneg _) _))]
    exact moment_bound_pt hs hμ0 hμ2 z

lemma integral_G_mul_rpow_le {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) :
    ∫ z : Eu d, G d s z * ‖z‖ ^ μ ≤ gm d * s ^ (μ / 2) := by
  have hI2 : Integrable (fun z : Eu d => G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z) :=
    (integrable_G hs).add ((integrable_G (by positivity)).const_mul _)
  calc ∫ z : Eu d, G d s z * ‖z‖ ^ μ
      ≤ ∫ z : Eu d, s ^ (μ / 2) * (G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z) :=
        integral_mono (integrable_G_mul_rpow hs hμ0 hμ2) (hI2.const_mul _)
          (fun z => moment_bound_pt hs hμ0 hμ2 z)
    _ = gm d * s ^ (μ / 2) := by
        rw [integral_const_mul, integral_add (integrable_G hs)
          ((integrable_G (by positivity)).const_mul _), integral_const_mul,
          integral_G hs, integral_G (by positivity), gm]
        ring

lemma integrable_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Eu d) :
    Integrable (fun y : Eu d => G d s (x - y)) :=
  (integrable_G hs).comp_sub_left x

lemma integral_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Eu d) :
    ∫ y : Eu d, G d s (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z => G d s z) volume x, integral_G hs]

lemma integrable_G_sub_mul_rpow {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (x : Eu d) : Integrable (fun y : Eu d => G d s (x - y) * ‖x - y‖ ^ μ) :=
  (integrable_G_mul_rpow hs hμ0 hμ2).comp_sub_left x

lemma integral_G_sub_mul_rpow_le {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (x : Eu d) : ∫ y : Eu d, G d s (x - y) * ‖x - y‖ ^ μ ≤ gm d * s ^ (μ / 2) := by
  rw [integral_sub_left_eq_self (fun z => G d s z * ‖z‖ ^ μ) volume x]
  exact integral_G_mul_rpow_le hs hμ0 hμ2

lemma integrableOn_rpow_mul_exp {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * rexp (-(r * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r)
    (by linarith) one_pos hr
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [rpow_one, neg_mul]

lemma integral_rpow_mul_exp {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ t in Ioi 0, t ^ (a - 1) * rexp (-(r * t)) = (1 / r) ^ a * Real.Gamma a :=
  Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr

lemma integrableOn_Ioc_rpow {p τ : ℝ} (hp : -1 < p) (hτ : 0 < τ) :
    IntegrableOn (fun t : ℝ => t ^ p) (Ioc 0 τ) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).mp (intervalIntegral.intervalIntegrable_rpow' hp)

lemma integral_Ioc_rpow {p τ : ℝ} (hp : -1 < p) (hτ : 0 < τ) :
    ∫ t in Ioc 0 τ, t ^ p = τ ^ (p + 1) / (p + 1) := by
  rw [← intervalIntegral.integral_of_le hτ.le, integral_rpow (Or.inl hp),
    zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]

/-- Splitting a time integral at `τ`: a `t^p` bound near `0` (`p > -1`) and a `t^q` bound near
infinity (`q < -1`). -/
lemma split_time_bound {F : ℝ → ℝ} {A B p q τ : ℝ}
    (hp : -1 < p) (hq : q < -1) (hτ : 0 < τ)
    (hm : AEStronglyMeasurable F (volume.restrict (Ioi 0)))
    (h1 : ∀ t, 0 < t → |F t| ≤ A * t ^ p) (h2 : ∀ t, 0 < t → |F t| ≤ B * t ^ q) :
    IntegrableOn F (Ioi 0) ∧
      |∫ t in Ioi 0, F t| ≤ A * (τ ^ (p + 1) / (p + 1)) + B * (-τ ^ (q + 1) / (q + 1)) := by
  have I1 : IntegrableOn (fun t : ℝ => A * t ^ p) (Ioc 0 τ) :=
    (integrableOn_Ioc_rpow hp hτ).const_mul A
  have I2 : IntegrableOn (fun t : ℝ => B * t ^ q) (Ioi τ) :=
    (integrableOn_Ioi_rpow_of_lt hq hτ).const_mul B
  have b1 : ∀ᵐ t ∂(volume.restrict (Ioc 0 τ)), ‖F t‖ ≤ A * t ^ p :=
    (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => by rw [Real.norm_eq_abs]; exact h1 t ht.1)
  have b2 : ∀ᵐ t ∂(volume.restrict (Ioi τ)), ‖F t‖ ≤ B * t ^ q :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]; exact h2 t (hτ.trans ht))
  have F1 : IntegrableOn F (Ioc 0 τ) :=
    I1.mono' (hm.mono_set Ioc_subset_Ioi_self) b1
  have F2 : IntegrableOn F (Ioi τ) :=
    I2.mono' (hm.mono_set (Ioi_subset_Ioi hτ.le)) b2
  have hU : Ioi (0 : ℝ) = Ioc 0 τ ∪ Ioi τ := (Ioc_union_Ioi_eq_Ioi hτ.le).symm
  refine ⟨hU ▸ F1.union F2, ?_⟩
  rw [hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi F1 F2]
  have e1 : ‖∫ t in Ioc 0 τ, F t‖ ≤ ∫ t in Ioc 0 τ, A * t ^ p := norm_integral_le_of_norm_le I1 b1
  have e2 : ‖∫ t in Ioi τ, F t‖ ≤ ∫ t in Ioi τ, B * t ^ q := norm_integral_le_of_norm_le I2 b2
  rw [integral_const_mul, integral_Ioc_rpow hp hτ] at e1
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hq hτ] at e2
  rw [Real.norm_eq_abs] at e1 e2
  exact (abs_add_le _ _).trans (add_le_add e1 e2)

/-- `min(a, b) ≤ a^(1-θ) b^θ` for `a, b ≥ 0`, `θ ∈ [0,1]`. -/
lemma min_le_rpow_mul_rpow {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    min a b ≤ a ^ (1 - θ) * b ^ θ := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    calc a = a ^ (1 - θ) * a ^ θ := by
          rcases ha.eq_or_lt with h | h
          · subst h
            rcases h0.eq_or_lt with h' | h'
            · subst h'; simp
            · rw [zero_rpow h'.ne']; simp
          · rw [← rpow_add h]; simp
      _ ≤ a ^ (1 - θ) * b ^ θ :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow ha hab h0) (rpow_nonneg ha _)
  · rw [min_eq_right hab]
    calc b = b ^ (1 - θ) * b ^ θ := by
          rcases hb.eq_or_lt with h | h
          · subst h
            rcases (sub_nonneg.mpr h1).eq_or_lt with h' | h'
            · have : θ = 1 := by linarith
              subst this; simp
            · rw [zero_rpow h'.ne']; simp
          · rw [← rpow_add h]; simp
      _ ≤ a ^ (1 - θ) * b ^ θ :=
          mul_le_mul_of_nonneg_right (rpow_le_rpow hb hab (by linarith)) (rpow_nonneg hb _)

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

/-- Hypotheses on a kernel family `K t x y` (time `t > 0`) with `x`-derivatives `K1 K2 K3`
and Gaussian bounds on the convex set `S`. -/
structure KHyp (d : ℕ) (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ)
    (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ))
    (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)) (A c : ℝ) : Prop where
  hA : 0 ≤ A
  hc : 0 < c
  hS : MeasurableSet S
  hconv : Convex ℝ S
  d1 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K t x y) (K1 t x y) x
  d2 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x
  d3 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x
  b0 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y)
  b1 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y)
  b2 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y)
  b3 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G d (c * t) (x - y)
  m0 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K p.1 x p.2)
  m1 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K1 p.1 x p.2)
  m2 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K2 p.1 x p.2)
  m3 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2)
  dom : ∀ t, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, IntegrableOn F S ∧
    ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧
      ‖K2 t x y‖ ≤ F y ∧ ‖K3 t x y‖ ≤ F y
  heat : ∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => K t x y)
    ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t
  mass : ∀ t, 0 < t → ∀ x, ∫ y in S, K t x y = 1

/-- `h` is bounded by `M0` and `μ`-Hölder with constant `Hh` on `S`. -/
def HolderOnS {d : ℕ} (S : Set (Eu d)) (μ M0 Hh : ℝ) (h : Eu d → ℝ) : Prop :=
  0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ

lemma integrableOn_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (S : Set (Eu d)) (x : Eu d) :
    IntegrableOn (fun y : Eu d => G d s (x - y)) S :=
  (integrable_G_sub hs x).integrableOn

lemma setIntegral_G_sub_le {d : ℕ} {s : ℝ} (hs : 0 < s) (S : Set (Eu d)) (x : Eu d) :
    ∫ y in S, G d s (x - y) ≤ 1 := by
  calc ∫ y in S, G d s (x - y) ≤ ∫ y, G d s (x - y) :=
        setIntegral_le_integral (integrable_G_sub hs x)
          (Eventually.of_forall fun y => G_nonneg hs _)
    _ = 1 := integral_G_sub hs x

lemma setIntegral_G_sub_mul_rpow_le {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (S : Set (Eu d)) (x : Eu d) :
    ∫ y in S, G d s (x - y) * ‖x - y‖ ^ μ ≤ gm d * s ^ (μ / 2) := by
  calc ∫ y in S, G d s (x - y) * ‖x - y‖ ^ μ ≤ ∫ y, G d s (x - y) * ‖x - y‖ ^ μ :=
        setIntegral_le_integral (integrable_G_sub_mul_rpow hs hμ0 hμ2 x)
          (Eventually.of_forall fun y =>
            mul_nonneg (G_nonneg hs _) (rpow_nonneg (norm_nonneg _) _))
    _ ≤ gm d * s ^ (μ / 2) := integral_G_sub_mul_rpow_le hs hμ0 hμ2 x

/-- Sup bound: `‖∫_S f • L‖ ≤ B M` when `‖L y‖ ≤ B G(s, x - y)` and `|f| ≤ M` on `S`. -/
lemma sup_bound {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {S : Set (Eu d)} (hS : MeasurableSet S) {L : Eu d → F'} {f : Eu d → ℝ} {x : Eu d}
    {B s M : ℝ} (hs : 0 < s) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hL : AEStronglyMeasurable L (volume.restrict S))
    (hf : AEStronglyMeasurable f (volume.restrict S))
    (hLb : ∀ y ∈ S, ‖L y‖ ≤ B * G d s (x - y)) (hfb : ∀ y ∈ S, |f y| ≤ M) :
    Integrable (fun y => f y • L y) (volume.restrict S) ∧
      ‖∫ y in S, f y • L y‖ ≤ B * M := by
  have hI : Integrable (fun y => M * B * G d s (x - y)) (volume.restrict S) :=
    (integrableOn_G_sub hs S x).const_mul (M * B)
  have hpt : ∀ᵐ y ∂(volume.restrict S), ‖f y • L y‖ ≤ M * B * G d s (x - y) :=
    (ae_restrict_iff' hS).mpr (Eventually.of_forall fun y hy => by
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul (hfb y hy) (hLb y hy) (norm_nonneg _) hM)
  refine ⟨hI.mono' (hf.smul hL) hpt, ?_⟩
  calc ‖∫ y in S, f y • L y‖ ≤ ∫ y in S, M * B * G d s (x - y) := norm_integral_le_of_norm_le hI hpt
    _ = M * B * ∫ y in S, G d s (x - y) := integral_const_mul _ _
    _ ≤ M * B * 1 := mul_le_mul_of_nonneg_left (setIntegral_G_sub_le hs S x) (by positivity)
    _ = B * M := by ring

/-- Zero-mean bound: `‖∫_S (h y - h x) • L y‖ ≤ B Hh gm s^(μ/2)`. -/
lemma zm_bound {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {S : Set (Eu d)} (hS : MeasurableSet S) {L : Eu d → F'} {h : Eu d → ℝ} {x : Eu d}
    {B s Hh μ : ℝ} (hs : 0 < s) (hB : 0 ≤ B) (hHh : 0 ≤ Hh) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (hL : AEStronglyMeasurable L (volume.restrict S))
    (hhm : AEStronglyMeasurable h (volume.restrict S))
    (hLb : ∀ y ∈ S, ‖L y‖ ≤ B * G d s (x - y))
    (hH : ∀ y ∈ S, |h y - h x| ≤ Hh * ‖x - y‖ ^ μ) :
    Integrable (fun y => (h y - h x) • L y) (volume.restrict S) ∧
      ‖∫ y in S, (h y - h x) • L y‖ ≤ B * Hh * (gm d * s ^ (μ / 2)) := by
  have hI : Integrable (fun y => B * Hh * (G d s (x - y) * ‖x - y‖ ^ μ)) (volume.restrict S) :=
    ((integrable_G_sub_mul_rpow hs hμ0 hμ2 x).integrableOn).const_mul (B * Hh)
  have hpt : ∀ᵐ y ∂(volume.restrict S),
      ‖(h y - h x) • L y‖ ≤ B * Hh * (G d s (x - y) * ‖x - y‖ ^ μ) :=
    (ae_restrict_iff' hS).mpr (Eventually.of_forall fun y hy => by
      rw [norm_smul, Real.norm_eq_abs]
      calc |h y - h x| * ‖L y‖ ≤ (Hh * ‖x - y‖ ^ μ) * (B * G d s (x - y)) :=
            mul_le_mul (hH y hy) (hLb y hy) (norm_nonneg _)
              (mul_nonneg hHh (rpow_nonneg (norm_nonneg _) _))
        _ = B * Hh * (G d s (x - y) * ‖x - y‖ ^ μ) := by ring)
  refine ⟨hI.mono' ((hhm.sub aestronglyMeasurable_const).smul hL) hpt, ?_⟩
  calc ‖∫ y in S, (h y - h x) • L y‖
      ≤ ∫ y in S, B * Hh * (G d s (x - y) * ‖x - y‖ ^ μ) := norm_integral_le_of_norm_le hI hpt
    _ = B * Hh * ∫ y in S, G d s (x - y) * ‖x - y‖ ^ μ := integral_const_mul _ _
    _ ≤ B * Hh * (gm d * s ^ (μ / 2)) :=
        mul_le_mul_of_nonneg_left (setIntegral_G_sub_mul_rpow_le hs hμ0 hμ2 S x)
          (mul_nonneg hB hHh)

/-- Differentiation under `∫_S` of `x ↦ ∫_S h y • L x y` with a local integrable bound. -/
lemma hasFDerivAt_kint {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] {S : Set (Eu d)} (hS : MeasurableSet S) {L : Eu d → Eu d → F'}
    {L' : Eu d → Eu d → (Eu d →L[ℝ] F')} {h : Eu d → ℝ} {M0 : ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0)
    (hLm : ∀ x, AEStronglyMeasurable (L x) (volume.restrict S))
    (hL'm : ∀ x, AEStronglyMeasurable (L' x) (volume.restrict S))
    (hd : ∀ x y, HasFDerivAt (fun x => L x y) (L' x y) x)
    {x₀ : Eu d} {r : ℝ} (hr : 0 < r) {F : Eu d → ℝ} (hF : IntegrableOn F S)
    (hLb : ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, ‖L x y‖ ≤ F y)
    (hL'b : ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, ‖L' x y‖ ≤ F y) :
    HasFDerivAt (fun x => ∫ y in S, h y • L x y) (∫ y in S, h y • L' x₀ y) x₀ := by
  have hM0 : ∀ y ∈ S, 0 ≤ M0 := fun y hy => (abs_nonneg _).trans (hhb y hy)
  have hFint : Integrable (fun y => M0 * F y) (volume.restrict S) := hF.const_mul M0
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x y => h y • L x y)
    (F' := fun x y => h y • L' x y) (Metric.ball_mem_nhds x₀ hr)
    (Eventually.of_forall fun x => hh.smul (hLm x)) ?_ (hh.smul (hL'm x₀)) ?_ hFint ?_
  · refine hFint.mono' (hh.smul (hLm x₀)) ((ae_restrict_iff' hS).mpr
      (Eventually.of_forall fun y hy => ?_))
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hhb y hy) (hLb x₀ (Metric.mem_ball_self hr) y hy) (norm_nonneg _) (hM0 y hy)
  · refine (ae_restrict_iff' hS).mpr (Eventually.of_forall fun y hy x hx => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hhb y hy) (hL'b x hx y hy) (norm_nonneg _) (hM0 y hy)
  · exact Eventually.of_forall fun y x _ => (hd x y).const_smul (h y)

section KernelInt

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}

lemma KHyp.sm0 (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d) :
    StronglyMeasurable (fun y => K t x y) :=
  (KH.m0 x).comp_measurable measurable_prodMk_left

lemma KHyp.sm1 (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d) :
    StronglyMeasurable (fun y => K1 t x y) :=
  (KH.m1 x).comp_measurable measurable_prodMk_left

lemma KHyp.sm2 (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d) :
    StronglyMeasurable (fun y => K2 t x y) :=
  (KH.m2 x).comp_measurable measurable_prodMk_left

lemma KHyp.sm3 (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d) :
    StronglyMeasurable (fun y => K3 t x y) :=
  (KH.m3 x).comp_measurable measurable_prodMk_left

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

lemma KHyp.hasFDerivAt_kw0 (KH : KHyp d S K K1 K2 K3 A c)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0)
    {t : ℝ} (ht : 0 < t) (x : Eu d) : HasFDerivAt (kw0 S K h t) (kw1 S K1 h t x) x := by
  obtain ⟨r, hr, F, hF, hb⟩ := KH.dom t ht x
  unfold kw0 kw1
  exact hasFDerivAt_kint KH.hS hh hhb (fun x => (KH.sm0 t x).aestronglyMeasurable)
    (fun x => (KH.sm1 t x).aestronglyMeasurable) (KH.d1 t ht) hr hF
    (fun x hx y hy => by rw [Real.norm_eq_abs]; exact (hb x hx y hy).1)
    (fun x hx y hy => (hb x hx y hy).2.1)

lemma KHyp.hasFDerivAt_kw1 (KH : KHyp d S K K1 K2 K3 A c)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0)
    {t : ℝ} (ht : 0 < t) (x : Eu d) : HasFDerivAt (kw1 S K1 h t) (kw2 S K2 h t x) x := by
  obtain ⟨r, hr, F, hF, hb⟩ := KH.dom t ht x
  unfold kw1 kw2
  exact hasFDerivAt_kint KH.hS hh hhb (fun x => (KH.sm1 t x).aestronglyMeasurable)
    (fun x => (KH.sm2 t x).aestronglyMeasurable) (KH.d2 t ht) hr hF
    (fun x hx y hy => (hb x hx y hy).2.1) (fun x hx y hy => (hb x hx y hy).2.2.1)

lemma KHyp.hasFDerivAt_kw2 (KH : KHyp d S K K1 K2 K3 A c)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0)
    {t : ℝ} (ht : 0 < t) (x : Eu d) : HasFDerivAt (kw2 S K2 h t) (kw3 S K3 h t x) x := by
  obtain ⟨r, hr, F, hF, hb⟩ := KH.dom t ht x
  unfold kw2 kw3
  exact hasFDerivAt_kint KH.hS hh hhb (fun x => (KH.sm2 t x).aestronglyMeasurable)
    (fun x => (KH.sm3 t x).aestronglyMeasurable) (KH.d3 t ht) hr hF
    (fun x hx y hy => (hb x hx y hy).2.2.1) (fun x hx y hy => (hb x hx y hy).2.2.2)

/-- Zero mean of the first derivative kernel. -/
lemma KHyp.int_K1 (KH : KHyp d S K K1 K2 K3 A c) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    ∫ y in S, K1 t x y = 0 := by
  have h1 := KH.hasFDerivAt_kw0 (h := fun _ => 1) (M0 := 1) aestronglyMeasurable_const
    (fun _ _ => by simp) ht x
  have hc : kw0 S K (fun _ => 1) t = fun _ => 1 := by
    funext z; simp only [kw0, one_smul]; exact KH.mass t ht z
  rw [hc] at h1
  have := h1.unique (hasFDerivAt_const _ x)
  simpa [kw1] using this

lemma KHyp.int_K2 (KH : KHyp d S K K1 K2 K3 A c) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    ∫ y in S, K2 t x y = 0 := by
  have h1 := KH.hasFDerivAt_kw1 (h := fun _ => 1) (M0 := 1) aestronglyMeasurable_const
    (fun _ _ => by simp) ht x
  have hc : kw1 S K1 (fun _ => 1) t = fun _ => 0 := by
    funext z; simp only [kw1, one_smul]; exact KH.int_K1 ht z
  rw [hc] at h1
  have := h1.unique (hasFDerivAt_const _ x)
  simpa [kw2] using this

lemma KHyp.int_K3 (KH : KHyp d S K K1 K2 K3 A c) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    ∫ y in S, K3 t x y = 0 := by
  have h1 := KH.hasFDerivAt_kw2 (h := fun _ => 1) (M0 := 1) aestronglyMeasurable_const
    (fun _ _ => by simp) ht x
  have hc : kw2 S K2 (fun _ => 1) t = fun _ => 0 := by
    funext z; simp only [kw2, one_smul]; exact KH.int_K2 ht z
  rw [hc] at h1
  have := h1.unique (hasFDerivAt_const _ x)
  simpa [kw3] using this

end KernelInt

lemma zm_rewrite {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] {S : Set (Eu d)} {L : Eu d → F'} {h : Eu d → ℝ} (x : Eu d)
    (hL : Integrable L (volume.restrict S))
    (hhL : Integrable (fun y => h y • L y) (volume.restrict S))
    (h0 : ∫ y in S, L y = 0) :
    ∫ y in S, h y • L y = ∫ y in S, (h y - h x) • L y := by
  have hL2 : Integrable (fun y => h x • L y) (volume.restrict S) := hL.smul (h x)
  simp_rw [sub_smul]
  rw [integral_sub hhL hL2, integral_smul, h0, smul_zero, sub_zero]

/-- Generic Hölder (zero-mean) bound for `∫_S h • L` with a Gaussian-bounded, mean-zero `L`. -/
lemma kint_hol_bound {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] {S : Set (Eu d)} (hS : MeasurableSet S) {L : Eu d → F'}
    {h : Eu d → ℝ} {x : Eu d} (hx : x ∈ S) {B s μ M0 Hh : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S))
    (hLm : AEStronglyMeasurable L (volume.restrict S))
    (hLb : ∀ y ∈ S, ‖L y‖ ≤ B * G d s (x - y)) (h0 : ∫ y in S, L y = 0) :
    ‖∫ y in S, h y • L y‖ ≤ B * Hh * (gm d * s ^ (μ / 2)) := by
  obtain ⟨hM0, hHh, hb, hH⟩ := hhol
  have hLi : Integrable L (volume.restrict S) :=
    ((integrableOn_G_sub hs S x).const_mul B).mono' hLm
      ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun y hy => hLb y hy))
  have hhL := (sup_bound hS hs hB hM0 hLm hh hLb hb).1
  rw [zm_rewrite x hLi hhL h0]
  refine (zm_bound hS hs hB hHh hμ0 hμ2 hLm hh hLb fun y hy => ?_).2
  rw [norm_sub_rev]; exact hH y hy x hx

section KernelBounds

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

lemma KHyp.kw0_le (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ S) : |kw0 S K h t x| ≤ A * M0 := by
  have := (sup_bound KH.hS (mul_pos KH.hc ht) KH.hA hhol.1 (KH.sm0 t x).aestronglyMeasurable hh
    (fun y hy => by rw [Real.norm_eq_abs]; exact KH.b0 t ht x hx y hy) hhol.2.2.1).2
  rwa [Real.norm_eq_abs] at this

lemma KHyp.kw1_le (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ S) : ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0 :=
  (sup_bound KH.hS (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hhol.1
    (KH.sm1 t x).aestronglyMeasurable hh (fun y hy => KH.b1 t ht x hx y hy) hhol.2.2.1).2

lemma KHyp.kw2_le (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ S) : ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * M0 :=
  (sup_bound KH.hS (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hhol.1
    (KH.sm2 t x).aestronglyMeasurable hh (fun y hy => KH.b2 t ht x hx y hy) hhol.2.2.1).2

lemma KHyp.kw2_hol (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S) :
    ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) :=
  kint_hol_bound KH.hS hx (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hμ0 hμ2
    hhol hh (KH.sm2 t x).aestronglyMeasurable (fun y hy => KH.b2 t ht x hx y hy) (KH.int_K2 ht x)

lemma KHyp.kw3_hol (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S) :
    ‖kw3 S K3 h t x‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) :=
  kint_hol_bound KH.hS hx (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hμ0 hμ2
    hhol hh (KH.sm3 t x).aestronglyMeasurable (fun y hy => KH.b3 t ht x hx y hy) (KH.int_K3 ht x)

end KernelBounds

/-- Generic Laplace-transform bound. -/
lemma time_sup_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {B a lam : ℝ} (ha : 0 < a) (hlam : 0 < lam)
    (hm : AEStronglyMeasurable F (volume.restrict (Ioi 0)))
    (hb : ∀ t, 0 < t → ‖F t‖ ≤ B * t ^ (a - 1)) :
    IntegrableOn (fun t => rexp (-(lam * t)) • F t) (Ioi 0) ∧
      ‖∫ t in Ioi 0, rexp (-(lam * t)) • F t‖ ≤ B * ((1 / lam) ^ a * Real.Gamma a) := by
  have hI : IntegrableOn (fun t : ℝ => B * (t ^ (a - 1) * rexp (-(lam * t)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp ha hlam).const_mul B
  have hpt : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ‖rexp (-(lam * t)) • F t‖ ≤ B * (t ^ (a - 1) * rexp (-(lam * t))) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      calc rexp (-(lam * t)) * ‖F t‖ ≤ rexp (-(lam * t)) * (B * t ^ (a - 1)) :=
            mul_le_mul_of_nonneg_left (hb t ht) (exp_pos _).le
        _ = B * (t ^ (a - 1) * rexp (-(lam * t))) := by ring)
  have hem : AEStronglyMeasurable (fun t : ℝ => rexp (-(lam * t))) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun t : ℝ => rexp (-(lam * t))).aestronglyMeasurable
  refine ⟨hI.mono' (hem.smul hm) hpt, ?_⟩
  calc ‖∫ t in Ioi 0, rexp (-(lam * t)) • F t‖
      ≤ ∫ t in Ioi 0, B * (t ^ (a - 1) * rexp (-(lam * t))) := norm_integral_le_of_norm_le hI hpt
    _ = B * ((1 / lam) ^ a * Real.Gamma a) := by
        rw [integral_const_mul, integral_rpow_mul_exp ha hlam]

/-- Difference of two Laplace transforms. -/
lemma time_diff_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F1 F2 : ℝ → E} {B a lam : ℝ} (ha : 0 < a) (hlam : 0 < lam)
    (hm1 : AEStronglyMeasurable F1 (volume.restrict (Ioi 0)))
    (hm2 : AEStronglyMeasurable F2 (volume.restrict (Ioi 0)))
    (hi1 : IntegrableOn (fun t => rexp (-(lam * t)) • F1 t) (Ioi 0))
    (hi2 : IntegrableOn (fun t => rexp (-(lam * t)) • F2 t) (Ioi 0))
    (hb : ∀ t, 0 < t → ‖F1 t - F2 t‖ ≤ B * t ^ (a - 1)) :
    ‖(∫ t in Ioi 0, rexp (-(lam * t)) • F1 t) - ∫ t in Ioi 0, rexp (-(lam * t)) • F2 t‖
      ≤ B * ((1 / lam) ^ a * Real.Gamma a) := by
  rw [← integral_sub hi1 hi2]
  simp_rw [← smul_sub]
  exact (time_sup_bound (F := fun t => F1 t - F2 t) ha hlam (hm1.sub hm2) hb).2

lemma rpow_neg_one_mul_rpow {c t μ : ℝ} (hc : 0 < c) (ht : 0 < t) :
    t ^ (-(1 : ℝ)) * (c * t) ^ (μ / 2) = c ^ (μ / 2) * t ^ (μ / 2 - 1) := by
  rw [mul_rpow hc.le ht.le, sub_eq_add_neg, rpow_add ht]; ring

section TimeK

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

lemma KHyp.tm0 (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S))
    (x : Eu d) : AEStronglyMeasurable (fun t => kw0 S K h t x) (volume.restrict (Ioi 0)) := by
  unfold kw0
  exact AEStronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × Eu d => h p.2 • K p.1 x p.2)
    (hh.comp_snd.smul (KH.m0 x).aestronglyMeasurable)

lemma KHyp.tm1 (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S))
    (x : Eu d) : AEStronglyMeasurable (fun t => kw1 S K1 h t x) (volume.restrict (Ioi 0)) := by
  unfold kw1
  exact AEStronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × Eu d => h p.2 • K1 p.1 x p.2)
    (hh.comp_snd.smul (KH.m1 x).aestronglyMeasurable)

lemma KHyp.tm2 (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S))
    (x : Eu d) : AEStronglyMeasurable (fun t => kw2 S K2 h t x) (volume.restrict (Ioi 0)) := by
  unfold kw2
  exact AEStronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × Eu d => h p.2 • K2 p.1 x p.2)
    (hh.comp_snd.smul (KH.m2 x).aestronglyMeasurable)

lemma KHyp.kw0_lip (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x x' : Eu d}
    (hx : x ∈ S) (hx' : x' ∈ S) :
    ‖kw0 S K h t x - kw0 S K h t x'‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0 * ‖x - x'‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (KH.hasFDerivAt_kw0 hh hhol.2.2.1 ht z).hasFDerivWithinAt)
    (fun z hz => KH.kw1_le hhol hh ht hz) KH.hconv hx' hx

lemma KHyp.kw1_lip (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x x' : Eu d}
    (hx : x ∈ S) (hx' : x' ∈ S) :
    ‖kw1 S K1 h t x - kw1 S K1 h t x'‖ ≤ A * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (KH.hasFDerivAt_kw1 hh hhol.2.2.1 ht z).hasFDerivWithinAt)
    (fun z hz => KH.kw2_le hhol hh ht hz) KH.hconv hx' hx

lemma KHyp.kw2_lip (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x x' : Eu d} (hx : x ∈ S) (hx' : x' ∈ S) :
    ‖kw2 S K2 h t x - kw2 S K2 h t x'‖
      ≤ A * t ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) * ‖x - x'‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (KH.hasFDerivAt_kw2 hh hhol.2.2.1 ht z).hasFDerivWithinAt)
    (fun z hz => KH.kw3_hol hhol hh hμ0 hμ2 ht hz) KH.hconv hx' hx

/-- The time integrals (resolvent candidates). -/
noncomputable def tu0 (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ) (h : Eu d → ℝ) (lam : ℝ)
    (x : Eu d) : ℝ := ∫ t in Ioi 0, rexp (-(lam * t)) • kw0 S K h t x

noncomputable def tu1 (S : Set (Eu d)) (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)) (h : Eu d → ℝ)
    (lam : ℝ) (x : Eu d) : Eu d →L[ℝ] ℝ := ∫ t in Ioi 0, rexp (-(lam * t)) • kw1 S K1 h t x

noncomputable def tu2 (S : Set (Eu d)) (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (h : Eu d → ℝ) (lam : ℝ) (x : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ t in Ioi 0, rexp (-(lam * t)) • kw2 S K2 h t x

variable {lam : ℝ}

lemma KHyp.tu0_sup (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hlam : 0 < lam) {x : Eu d} (hx : x ∈ S) :
    IntegrableOn (fun t => rexp (-(lam * t)) • kw0 S K h t x) (Ioi 0) ∧
      ‖tu0 S K h lam x‖ ≤ A * M0 * ((1 / lam) ^ (1 : ℝ) * Real.Gamma 1) :=
  time_sup_bound one_pos hlam (KH.tm0 hh x) fun t ht => by
    rw [sub_self, rpow_zero, mul_one, Real.norm_eq_abs]; exact KH.kw0_le hhol hh ht hx

lemma KHyp.tu1_sup (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hlam : 0 < lam) {x : Eu d} (hx : x ∈ S) :
    IntegrableOn (fun t => rexp (-(lam * t)) • kw1 S K1 h t x) (Ioi 0) ∧
      ‖tu1 S K1 h lam x‖ ≤ A * M0 * ((1 / lam) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2)) :=
  time_sup_bound (by norm_num) hlam (KH.tm1 hh x) fun t ht => by
    have := KH.kw1_le hhol hh ht hx
    calc ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0 := this
      _ = A * M0 * t ^ ((1 / 2 : ℝ) - 1) := by norm_num; ring

lemma KHyp.tu2_sup (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2)
    (hlam : 0 < lam) {x : Eu d} (hx : x ∈ S) :
    IntegrableOn (fun t => rexp (-(lam * t)) • kw2 S K2 h t x) (Ioi 0) ∧
      ‖tu2 S K2 h lam x‖ ≤ A * Hh * gm d * c ^ (μ / 2) * ((1 / lam) ^ (μ / 2) * Real.Gamma (μ / 2)) :=
  time_sup_bound (by linarith) hlam (KH.tm2 hh x) fun t ht => by
    have := KH.kw2_hol hhol hh hμ0.le hμ2 ht hx
    calc ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) := this
      _ = A * Hh * gm d * (t ^ (-(1 : ℝ)) * (c * t) ^ (μ / 2)) := by ring
      _ = A * Hh * gm d * c ^ (μ / 2) * t ^ (μ / 2 - 1) := by
          rw [rpow_neg_one_mul_rpow KH.hc ht]; ring

end TimeK

/-- Pointwise interpolation of a sup bound and a Lipschitz bound. -/
lemma interp_bound {X a b r t p q μ e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (ht : 0 < t)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (he : p * (1 - μ) + q * μ = e)
    (h1 : X ≤ a * t ^ p) (h2 : X ≤ b * t ^ q * r) :
    X ≤ a ^ (1 - μ) * b ^ μ * r ^ μ * t ^ e := by
  calc X ≤ min (a * t ^ p) (b * t ^ q * r) := le_min h1 h2
    _ ≤ (a * t ^ p) ^ (1 - μ) * (b * t ^ q * r) ^ μ :=
        min_le_rpow_mul_rpow (by positivity) (by positivity) hμ0 hμ1
    _ = a ^ (1 - μ) * b ^ μ * r ^ μ * t ^ e := by
        rw [mul_rpow ha (by positivity), mul_rpow (by positivity) hr, mul_rpow hb (by positivity),
          ← rpow_mul ht.le, ← rpow_mul ht.le, ← he, rpow_add ht]; ring

section TimeHol

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

lemma KHyp.tu0_hol (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hlam : 0 < lam) {x x' : Eu d} (hx : x ∈ S) (hx' : x' ∈ S) :
    ‖tu0 S K h lam x - tu0 S K h lam x'‖ ≤ (2 * A * M0) ^ (1 - μ) * (A * M0) ^ μ * ‖x - x'‖ ^ μ
      * ((1 / lam) ^ (1 - μ / 2) * Real.Gamma (1 - μ / 2)) := by
  have hAM : 0 ≤ A * M0 := mul_nonneg KH.hA hhol.1
  refine time_diff_bound (by linarith) hlam (KH.tm0 hh x) (KH.tm0 hh x')
    (KH.tu0_sup hhol hh hlam hx).1 (KH.tu0_sup hhol hh hlam hx').1 fun t ht => ?_
  refine interp_bound (p := 0) (q := -(1 / 2)) (by have := KH.hA; have := hhol.1; positivity) hAM (norm_nonneg _) ht hμ0 hμ1
    (by ring) ?_ ?_
  · rw [rpow_zero, mul_one]
    calc ‖kw0 S K h t x - kw0 S K h t x'‖ ≤ ‖kw0 S K h t x‖ + ‖kw0 S K h t x'‖ := norm_sub_le _ _
      _ ≤ A * M0 + A * M0 := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          exact add_le_add (KH.kw0_le hhol hh ht hx) (KH.kw0_le hhol hh ht hx')
      _ = 2 * A * M0 := by ring
  · calc ‖kw0 S K h t x - kw0 S K h t x'‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0 * ‖x - x'‖ :=
          KH.kw0_lip hhol hh ht hx hx'
      _ = A * M0 * t ^ (-(1 / 2 : ℝ)) * ‖x - x'‖ := by ring

lemma KHyp.tu1_hol (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hlam : 0 < lam) {x x' : Eu d} (hx : x ∈ S) (hx' : x' ∈ S) :
    ‖tu1 S K1 h lam x - tu1 S K1 h lam x'‖ ≤ (2 * A * M0) ^ (1 - μ) * (A * M0) ^ μ * ‖x - x'‖ ^ μ
      * ((1 / lam) ^ ((1 - μ) / 2) * Real.Gamma ((1 - μ) / 2)) := by
  have hAM : 0 ≤ A * M0 := mul_nonneg KH.hA hhol.1
  refine time_diff_bound (by linarith) hlam (KH.tm1 hh x) (KH.tm1 hh x')
    (KH.tu1_sup hhol hh hlam hx).1 (KH.tu1_sup hhol hh hlam hx').1 fun t ht => ?_
  refine interp_bound (p := -(1 / 2)) (q := -1) (by have := KH.hA; have := hhol.1; positivity) hAM (norm_nonneg _) ht hμ0
    hμ1.le (by ring) ?_ ?_
  · calc ‖kw1 S K1 h t x - kw1 S K1 h t x'‖ ≤ ‖kw1 S K1 h t x‖ + ‖kw1 S K1 h t x'‖ :=
          norm_sub_le _ _
      _ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0 + A * t ^ (-(1 / 2 : ℝ)) * M0 :=
          add_le_add (KH.kw1_le hhol hh ht hx) (KH.kw1_le hhol hh ht hx')
      _ = 2 * A * M0 * t ^ (-(1 / 2 : ℝ)) := by ring
  · calc ‖kw1 S K1 h t x - kw1 S K1 h t x'‖ ≤ A * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖ :=
          KH.kw1_lip hhol hh ht hx hx'
      _ = A * M0 * t ^ (-1 : ℝ) * ‖x - x'‖ := by ring

lemma KHyp.tu2_hol (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hlam : 0 < lam) {x x' : Eu d} (hx : x ∈ S) (hx' : x' ∈ S) :
    ‖tu2 S K2 h lam x - tu2 S K2 h lam x'‖
      ≤ A * Hh * gm d * c ^ (μ / 2) * (2 / (μ / 2) + 1 / (1 / 2 - μ / 2)) * ‖x - x'‖ ^ μ := by
  set B := A * Hh * gm d * c ^ (μ / 2) with hBdef
  have hB : 0 ≤ B := by
    have := KH.hA; have := hhol.2.1; have := gm_pos d; have := KH.hc; positivity
  rcases eq_or_ne x x' with rfl | hne
  · rw [sub_self, sub_self, norm_zero, norm_zero, zero_rpow hμ0.ne', mul_zero]
  set r := ‖x - x'‖ with hrdef
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have i1 := (KH.tu2_sup hhol hh hμ0 (by linarith) hlam hx).1
  have i2 := (KH.tu2_sup hhol hh hμ0 (by linarith) hlam hx').1
  have hD : tu2 S K2 h lam x - tu2 S K2 h lam x' = ∫ t in Ioi 0,
      (rexp (-(lam * t)) • kw2 S K2 h t x - rexp (-(lam * t)) • kw2 S K2 h t x') :=
    (integral_sub i1 i2).symm
  have hsup : ∀ z ∈ S, ∀ t, 0 < t → ‖kw2 S K2 h t z‖ ≤ B * t ^ (μ / 2 - 1) := fun z hz t ht => by
    calc ‖kw2 S K2 h t z‖ ≤ A * t ^ (-(1 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) :=
          KH.kw2_hol hhol hh hμ0.le (by linarith) ht hz
      _ = A * Hh * gm d * (t ^ (-(1 : ℝ)) * (c * t) ^ (μ / 2)) := by ring
      _ = B * t ^ (μ / 2 - 1) := by rw [rpow_neg_one_mul_rpow KH.hc ht, hBdef]; ring
  have hlip : ∀ t, 0 < t → ‖kw2 S K2 h t x - kw2 S K2 h t x'‖ ≤ B * r * t ^ (μ / 2 - 3 / 2) :=
    fun t ht => by
      calc ‖kw2 S K2 h t x - kw2 S K2 h t x'‖
          ≤ A * t ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) * r :=
            KH.kw2_lip hhol hh hμ0.le (by linarith) ht hx hx'
        _ = B * r * t ^ (μ / 2 - 3 / 2) := by
            rw [mul_rpow KH.hc.le ht.le, hBdef,
              show μ / 2 - 3 / 2 = -(3 / 2 : ℝ) + μ / 2 by ring, rpow_add ht]; ring
  have hnD : ∀ t, 0 < t → ‖rexp (-(lam * t)) • kw2 S K2 h t x - rexp (-(lam * t)) • kw2 S K2 h t x'‖
      ≤ ‖kw2 S K2 h t x - kw2 S K2 h t x'‖ := fun t ht => by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (exp_le_one_iff.mpr (by nlinarith))
  have hD1 : ∀ t, 0 < t → |‖rexp (-(lam * t)) • kw2 S K2 h t x
      - rexp (-(lam * t)) • kw2 S K2 h t x'‖| ≤ 2 * B * t ^ (μ / 2 - 1) := fun t ht => by
    rw [abs_norm]
    calc _ ≤ ‖kw2 S K2 h t x - kw2 S K2 h t x'‖ := hnD t ht
      _ ≤ ‖kw2 S K2 h t x‖ + ‖kw2 S K2 h t x'‖ := norm_sub_le _ _
      _ ≤ B * t ^ (μ / 2 - 1) + B * t ^ (μ / 2 - 1) := add_le_add (hsup x hx t ht) (hsup x' hx' t ht)
      _ = 2 * B * t ^ (μ / 2 - 1) := by ring
  have hD2 : ∀ t, 0 < t → |‖rexp (-(lam * t)) • kw2 S K2 h t x
      - rexp (-(lam * t)) • kw2 S K2 h t x'‖| ≤ B * r * t ^ (μ / 2 - 3 / 2) := fun t ht => by
    rw [abs_norm]; exact (hnD t ht).trans (hlip t ht)
  obtain ⟨-, hbd⟩ := split_time_bound (p := μ / 2 - 1) (q := μ / 2 - 3 / 2) (τ := r ^ (2 : ℝ))
    (by linarith) (by linarith) (by positivity) ((i1.sub i2).aestronglyMeasurable.norm) hD1 hD2
  have e1 : (r ^ (2 : ℝ)) ^ (μ / 2 - 1 + 1) = r ^ μ := by
    rw [← rpow_mul hr.le]; congr 1; ring
  have e2 : (r ^ (2 : ℝ)) ^ (μ / 2 - 3 / 2 + 1) = r ^ μ / r := by
    rw [eq_div_iff hr.ne', ← rpow_mul hr.le]
    conv_lhs => rw [show r ^ (2 * (μ / 2 - 3 / 2 + 1)) * r = r ^ (2 * (μ / 2 - 3 / 2 + 1)) * r ^ (1 : ℝ)
      by rw [rpow_one]]
    rw [← rpow_add hr]; congr 1; ring
  rw [hD]
  calc _ ≤ ∫ t in Ioi 0, ‖rexp (-(lam * t)) • kw2 S K2 h t x
          - rexp (-(lam * t)) • kw2 S K2 h t x'‖ := norm_integral_le_integral_norm _
    _ ≤ |∫ t in Ioi 0, ‖rexp (-(lam * t)) • kw2 S K2 h t x
          - rexp (-(lam * t)) • kw2 S K2 h t x'‖| := le_abs_self _
    _ ≤ _ := hbd
    _ = B * (2 / (μ / 2) + 1 / (1 / 2 - μ / 2)) * r ^ μ := by
        rw [e1, e2]
        have h1 : μ / 2 - 1 + 1 = μ / 2 := by ring
        have h2 : μ / 2 - 3 / 2 + 1 = -(1 / 2 - μ / 2) := by ring
        have h3 : (1 / 2 - μ / 2) ≠ 0 := by linarith
        rw [h1, h2]
        field_simp

end TimeHol

/-- Trace of a bilinear form in the standard basis (twice the generator `Δ/2` acts as `lap2/2`). -/
noncomputable def lap2 {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

lemma continuous_lap2 {d : ℕ} : Continuous (lap2 (d := d)) := by
  unfold lap2; fun_prop

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

lemma lap2_smul {d : ℕ} (a : ℝ) (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : lap2 (a • B) = a * lap2 B := by
  unfold lap2; rw [Finset.mul_sum]; rfl

lemma lap2_integral {d : ℕ} {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {φ : α → Eu d →L[ℝ] Eu d →L[ℝ] ℝ} (hφ : Integrable φ ν) :
    lap2 (∫ a, φ a ∂ν) = ∫ a, lap2 (φ a) ∂ν := by
  unfold lap2
  rw [integral_finsetSum _ fun i _ =>
    (hφ.apply_continuousLinearMap _).apply_continuousLinearMap _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.integral_apply hφ, ContinuousLinearMap.integral_apply
    (hφ.apply_continuousLinearMap _)]

/-- Local comparison of Gaussians with nearby parameters. -/
lemma G_le_near {d : ℕ} {s s' : ℝ} (hs : 0 < s) (h1 : s / 2 ≤ s') (h2 : s' ≤ 2 * s) (z : Eu d) :
    G d s' z ≤ (4 : ℝ) ^ ((d : ℝ) / 2) * G d (2 * s) z := by
  unfold G
  have hs' : 0 < s' := by linarith
  have e1 : (π * s') ^ (-((d : ℝ) / 2)) ≤ (4 : ℝ) ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) := by
    calc (π * s') ^ (-((d : ℝ) / 2)) ≤ (π * (2 * s) / 4) ^ (-((d : ℝ) / 2)) :=
          rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [pi_pos]) (by
            have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      _ = (4 : ℝ) ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) := by
          rw [div_rpow (by positivity) (by norm_num), rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
          field_simp
  have e2 : rexp (-‖z‖ ^ 2 / s') ≤ rexp (-‖z‖ ^ 2 / (2 * s)) := by
    apply exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  calc (π * s') ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s')
      ≤ ((4 : ℝ) ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2))) * rexp (-‖z‖ ^ 2 / (2 * s)) :=
        mul_le_mul e1 e2 (exp_pos _).le (by positivity)
    _ = _ := by ring

section TimeDeriv

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

lemma KHyp.hasFDerivAt_tu0 (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hlam : 0 < lam) {x : Eu d} {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball x r ⊆ S) :
    HasFDerivAt (tu0 S K h lam) (tu1 S K1 h lam x) x := by
  have hem : AEStronglyMeasurable (fun t : ℝ => rexp (-(lam * t))) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun t : ℝ => rexp (-(lam * t))).aestronglyMeasurable
  unfold tu0 tu1
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => rexp (-(lam * t)) • kw0 S K h t x)
    (F' := fun x t => rexp (-(lam * t)) • kw1 S K1 h t x)
    (bound := fun t => A * M0 * (t ^ ((1 / 2 : ℝ) - 1) * rexp (-(lam * t))))
    (Metric.ball_mem_nhds x hr) (Eventually.of_forall fun x' => hem.smul (KH.tm0 hh x'))
    (KH.tu0_sup hhol hh hlam (hball (Metric.mem_ball_self hr))).1 (hem.smul (KH.tm1 hh x))
    ?_ ((integrableOn_rpow_mul_exp (by norm_num) hlam).const_mul _) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht x' hx' => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      calc rexp (-(lam * t)) * ‖kw1 S K1 h t x'‖
          ≤ rexp (-(lam * t)) * (A * t ^ (-(1 / 2 : ℝ)) * M0) :=
            mul_le_mul_of_nonneg_left (KH.kw1_le hhol hh ht (hball hx')) (exp_pos _).le
        _ = A * M0 * (t ^ ((1 / 2 : ℝ) - 1) * rexp (-(lam * t))) := by
            rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]; ring)
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht x' _ =>
      by have := (KH.hasFDerivAt_kw0 hh hhol.2.2.1 ht x').const_smul (rexp (-(lam * t)))
         exact this)

lemma KHyp.hasFDerivAt_tu1 (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (hlam : 0 < lam)
    {x : Eu d} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ S) :
    HasFDerivAt (tu1 S K1 h lam) (tu2 S K2 h lam x) x := by
  have hem : AEStronglyMeasurable (fun t : ℝ => rexp (-(lam * t))) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun t : ℝ => rexp (-(lam * t))).aestronglyMeasurable
  unfold tu1 tu2
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => rexp (-(lam * t)) • kw1 S K1 h t x)
    (F' := fun x t => rexp (-(lam * t)) • kw2 S K2 h t x)
    (bound := fun t => A * Hh * gm d * c ^ (μ / 2) * (t ^ (μ / 2 - 1) * rexp (-(lam * t))))
    (Metric.ball_mem_nhds x hr) (Eventually.of_forall fun x' => hem.smul (KH.tm1 hh x'))
    (KH.tu1_sup hhol hh hlam (hball (Metric.mem_ball_self hr))).1 (hem.smul (KH.tm2 hh x))
    ?_ ((integrableOn_rpow_mul_exp (by linarith) hlam).const_mul _) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht x' hx' => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      calc rexp (-(lam * t)) * ‖kw2 S K2 h t x'‖
          ≤ rexp (-(lam * t)) * (A * t ^ (-(1 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2))) :=
            mul_le_mul_of_nonneg_left (KH.kw2_hol hhol hh hμ0.le hμ2 ht (hball hx')) (exp_pos _).le
        _ = A * Hh * gm d * (t ^ (-(1 : ℝ)) * (c * t) ^ (μ / 2)) * rexp (-(lam * t)) := by ring
        _ = A * Hh * gm d * c ^ (μ / 2) * (t ^ (μ / 2 - 1) * rexp (-(lam * t))) := by
            rw [rpow_neg_one_mul_rpow KH.hc ht]; ring)
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht x' _ =>
      by have := (KH.hasFDerivAt_kw1 hh hhol.2.2.1 ht x').const_smul (rexp (-(lam * t)))
         exact this)

/-- `kw0 t x → h x`: quantitative form. -/
lemma KHyp.kw0_sub_h (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S) :
    |kw0 S K h t x - h x| ≤ A * Hh * (gm d * (c * t) ^ (μ / 2)) := by
  have hb : ∀ y ∈ S, ‖K t x y‖ ≤ A * G d (c * t) (x - y) := fun y hy => by
    rw [Real.norm_eq_abs]; exact KH.b0 t ht x hx y hy
  have hLm := (KH.sm0 t x).aestronglyMeasurable (μ := volume.restrict S)
  have hLi : Integrable (fun y => K t x y) (volume.restrict S) :=
    ((integrableOn_G_sub (mul_pos KH.hc ht) S x).const_mul A).mono' hLm
      ((ae_restrict_iff' KH.hS).mpr (Eventually.of_forall fun y hy => hb y hy))
  have hhL := (sup_bound KH.hS (mul_pos KH.hc ht) KH.hA hhol.1 hLm hh hb hhol.2.2.1).1
  have he : kw0 S K h t x - h x = ∫ y in S, (h y - h x) • K t x y := by
    unfold kw0
    simp_rw [sub_smul]
    have hLi' : Integrable (fun y => h x • K t x y) (volume.restrict S) := hLi.smul (h x)
    rw [integral_sub hhL hLi', integral_smul, KH.mass t ht x, smul_eq_mul, mul_one]
  rw [he, ← Real.norm_eq_abs]
  exact (zm_bound KH.hS (mul_pos KH.hc ht) KH.hA hhol.2.1 hμ0 hμ2 hLm hh hb fun y hy => by
    rw [norm_sub_rev]; exact hhol.2.2.2 y hy x hx).2

/-- Heat equation for the space integral: `∂_t kw0 = lap2 (kw2) / 2` on `S`. -/
lemma KHyp.hasDerivAt_kw0_t (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ S) :
    HasDerivAt (fun t => kw0 S K h t x) ((1 / 2 : ℝ) * lap2 (kw2 S K2 h t x)) t := by
  have hc := KH.hc
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set C := M0 * (1 / 2) * d * A * (2 / t) * (4 : ℝ) ^ ((d : ℝ) / 2) with hC
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun t y => h y * K t x y) (x₀ := t)
    (F' := fun t y => h y * ((1 / 2 : ℝ) * lap2 (K2 t x y)))
    (bound := fun y => C * G d (2 * (c * t)) (x - y)) (Ioo_mem_nhds (half_lt_self ht)
      (by linarith : t < 2 * t))
    (Eventually.of_forall fun t' => hh.mul (KH.sm0 t' x).aestronglyMeasurable)
    (sup_bound KH.hS (mul_pos KH.hc ht) KH.hA hhol.1 (KH.sm0 t x).aestronglyMeasurable hh
      (fun y hy => by rw [Real.norm_eq_abs]; exact KH.b0 t ht x hx y hy) hhol.2.2.1).1
    (hh.mul (aestronglyMeasurable_const.mul
      (continuous_lap2.comp_aestronglyMeasurable (KH.sm2 t x).aestronglyMeasurable)))
    ?_ ((integrableOn_G_sub (by positivity) S x).const_mul C) ?_
  · show HasDerivAt (fun n => ∫ y in S, h y * K n x y) _ t
    have hI2 := (sup_bound KH.hS (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _))
      hhol.1 (KH.sm2 t x).aestronglyMeasurable hh (fun y hy => KH.b2 t ht x hx y hy)
      hhol.2.2.1).1
    have e : ∫ y in S, h y * ((1 / 2 : ℝ) * lap2 (K2 t x y)) = (1 / 2 : ℝ) * lap2 (kw2 S K2 h t x) := by
      unfold kw2
      rw [lap2_integral hI2, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [lap2_smul]; ring
    rw [← e]
    exact key.2
  · refine (ae_restrict_iff' KH.hS).mpr (Eventually.of_forall fun y hy t' ht' => ?_)
    have ht'0 : 0 < t' := by linarith [ht'.1, half_pos ht]
    have hG := G_le_near (d := d) (mul_pos hc ht) (s' := c * t') (by nlinarith [ht'.1])
      (by nlinarith [ht'.2]) (x - y)
    have hK2 := KH.b2 t' ht'0 x hx y hy
    have hinv : t' ^ (-(1 : ℝ)) ≤ 2 / t := by
      rw [rpow_neg_one, inv_le_comm₀ ht'0 (by positivity)]
      have := ht'.1; rw [inv_div]; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hl := abs_lap2_le (K2 t' x y)
    have hGn := G_nonneg (d := d) (mul_pos hc ht'0) (x - y)
    have hG2n := G_nonneg (d := d) (by positivity : 0 < 2 * (c * t)) (x - y)
    have hA := KH.hA
    have hM := hhol.1
    calc |h y| * (1 / 2 * |lap2 (K2 t' x y)|)
        ≤ M0 * (1 / 2 * (d * (A * t' ^ (-(1 : ℝ)) * G d (c * t') (x - y)))) := by
          gcongr
          · exact hhol.2.2.1 y hy
          · exact hl.trans (mul_le_mul_of_nonneg_left hK2 hd)
      _ ≤ M0 * (1 / 2 * (d * (A * (2 / t) * ((4 : ℝ) ^ ((d : ℝ) / 2) * G d (2 * (c * t)) (x - y))))) := by
          gcongr
      _ = C * G d (2 * (c * t)) (x - y) := by rw [hC]; ring
  · exact (ae_restrict_iff' KH.hS).mpr (Eventually.of_forall fun y hy t' ht' =>
      (KH.heat t' (by linarith [ht'.1, half_pos ht]) x y).const_mul (h y))

end TimeDeriv

section TimeEq

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

lemma integrable_lap2 {d : ℕ} {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {φ : α → Eu d →L[ℝ] Eu d →L[ℝ] ℝ} (hφ : Integrable φ ν) : Integrable (fun a => lap2 (φ a)) ν :=
  (hφ.norm.const_mul (d : ℝ)).mono' (continuous_lap2.comp_aestronglyMeasurable hφ.aestronglyMeasurable)
    (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact abs_lap2_le _)

lemma KHyp.kw0_tendsto (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) {x : Eu d}
    (hx : x ∈ S) : Tendsto (fun t => kw0 S K h t x) (𝓝[>] 0) (𝓝 (h x)) := by
  have hg : Tendsto (fun t : ℝ => A * Hh * (gm d * (c * t) ^ (μ / 2))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => A * Hh * (gm d * (c * t) ^ (μ / 2)) :=
      continuous_const.mul (continuous_const.mul
        ((continuous_const.mul continuous_id).rpow_const fun _ => Or.inr (by linarith)))
    have := hc.tendsto 0
    simp only [mul_zero, zero_rpow (by linarith : μ / 2 ≠ 0)] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) ?_ hg)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.norm_eq_abs]
  exact KH.kw0_sub_h hhol hh hμ0.le hμ2 ht hx

/-- The resolvent equation on `S` (pointwise). -/
lemma KHyp.equation (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2)
    (hlam : 0 < lam) {x : Eu d} (hx : x ∈ S) :
    lam * tu0 S K h lam x - (1 / 2 : ℝ) * lap2 (tu2 S K2 h lam x) = h x := by
  set φ : ℝ → ℝ := fun t => rexp (-(lam * t)) * kw0 S K h t x with hφ
  set φ' : ℝ → ℝ := fun t => -lam * (rexp (-(lam * t)) • kw0 S K h t x)
    + (1 / 2 : ℝ) * lap2 (rexp (-(lam * t)) • kw2 S K2 h t x) with hφ'
  set f : ℝ → ℝ := fun t => if 0 < t then φ t else h x with hf
  have i0 := (KH.tu0_sup hhol hh hlam hx).1
  have i2 := (KH.tu2_sup hhol hh hμ0 hμ2 hlam hx).1
  have hder : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (φ' t) t := fun t ht => by
    have he : HasDerivAt (fun t => rexp (-(lam * t))) (rexp (-(lam * t)) * (-lam)) t := by
      have := ((hasDerivAt_id t).const_mul lam).neg.exp
      simpa using this
    have hp := he.mul (KH.hasDerivAt_kw0_t hhol hh ht hx)
    have hp' : HasDerivAt φ (φ' t) t := by
      refine hp.congr_deriv ?_
      simp only [hφ', lap2_smul, smul_eq_mul]; ring
    refine hp'.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp only [hf, if_pos (show (0 : ℝ) < s from hs)]
  have hint : IntegrableOn φ' (Ioi 0) :=
    (i0.const_mul (-lam)).add ((integrable_lap2 i2).const_mul (1 / 2 : ℝ))
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have h0 : f 0 = h x := by simp [hf]
    rw [ContinuousWithinAt, h0]
    have hlim : Tendsto φ (𝓝[>] 0) (𝓝 (h x)) := by
      have he : Tendsto (fun t : ℝ => rexp (-(lam * t))) (𝓝[>] 0) (𝓝 1) := by
        have : Continuous fun t : ℝ => rexp (-(lam * t)) := by fun_prop
        have := this.tendsto 0
        simp only [mul_zero, neg_zero, exp_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      simpa using he.mul (KH.kw0_tendsto hhol hh hμ0 hμ2 hx)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [hf, if_pos (show (0 : ℝ) < t from ht)]
  have hinf : Tendsto f atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => rexp (-(lam * t)) * (A * M0)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hlam)).mul_const (A * M0)
      simpa using this
    refine squeeze_zero_norm' ?_ he
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [hf, if_pos ht, hφ, norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (KH.kw0_le hhol hh ht hx) (exp_pos _).le
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hder hint hinf
  have h0 : f 0 = h x := by simp [hf]
  rw [h0] at key
  have hsplit : ∫ t in Ioi 0, φ' t = -lam * tu0 S K h lam x
      + (1 / 2 : ℝ) * lap2 (tu2 S K2 h lam x) := by
    rw [hφ', integral_add (i0.const_mul (-lam)) ((integrable_lap2 i2).const_mul (1 / 2 : ℝ)),
      integral_const_mul, integral_const_mul, tu2, lap2_integral i2]
    rfl
  rw [hsplit] at key
  linarith

end TimeEq

section KSMain

variable {d : ℕ}

lemma continuousOn_of_holder {S : Set (Eu d)} {h : Eu d → ℝ} {Hh μ : ℝ} (hμ0 : 0 < μ)
    (hhol : ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) : ContinuousOn h S := by
  intro x hx
  have hg : Tendsto (fun y : Eu d => Hh * ‖y - x‖ ^ μ) (𝓝[S] x) (𝓝 0) := by
    have hc : Continuous (fun y : Eu d => Hh * ‖y - x‖ ^ μ) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hμ0.le)
    have h0 : Tendsto (fun y : Eu d => Hh * ‖y - x‖ ^ μ) (𝓝[S] x) (𝓝 (Hh * ‖x - x‖ ^ μ)) :=
      (hc.tendsto x).mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow hμ0.ne'] using h0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.norm_eq_abs]; exact hhol y hy x hx

lemma abs_app_le (L : Eu d →L[ℝ] ℝ) (v : Eu d) : |L v| ≤ ‖L‖ * ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact L.le_opNorm v

lemma abs_app2_le (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (v w : Eu d) : |B v w| ≤ ‖B‖ * ‖v‖ * ‖w‖ := by
  rw [← Real.norm_eq_abs]; exact B.le_opNorm₂ v w

lemma fin_bound {a N k C X : ℝ} (h1 : a ≤ N) (h2 : N = k * X) (hk : k ≤ C) (hX : 0 ≤ X) :
    a ≤ C * X :=
  (h1.trans_eq h2).trans (mul_le_mul_of_nonneg_right hk hX)

lemma rpow_split {a b M μ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) :
    (a * M) ^ (1 - μ) * (b * M) ^ μ = a ^ (1 - μ) * b ^ μ * M := by
  rw [mul_rpow ha hM, mul_rpow hb hM]
  have hMM : M ^ (1 - μ) * M ^ μ = M := by
    rw [← rpow_add' hM (by rw [sub_add_cancel]; exact one_ne_zero), sub_add_cancel, rpow_one]
  calc a ^ (1 - μ) * M ^ (1 - μ) * (b ^ μ * M ^ μ) = a ^ (1 - μ) * b ^ μ * (M ^ (1 - μ) * M ^ μ) := by
        ring
    _ = a ^ (1 - μ) * b ^ μ * M := by rw [hMM]

lemma clm_integral_zero {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) {φ : α → E}
    (h : ∀ᵐ a ∂μ, L (φ a) = 0) : L (∫ a, φ a ∂μ) = 0 := by
  by_cases hφ : Integrable φ μ
  · rw [← L.integral_comp_comm hφ, integral_congr_ae h, integral_zero]
  · rw [integral_undef hφ, map_zero]

/-- A map into `Eu d →L F` is strongly measurable when all its applications are. -/
lemma sm_of_apply {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : α → (Eu d →L[ℝ] F)} (hg : ∀ v, StronglyMeasurable (fun a => g a v)) : StronglyMeasurable g := by
  have hrep : g = fun a => ∑ i : Fin d,
      (EuclideanSpace.proj i : Eu d →L[ℝ] ℝ).smulRight (g a (EuclideanSpace.single i 1)) := by
    funext a; ext v
    have hv := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
    rw [ContinuousLinearMap.sum_apply]
    conv_lhs => rw [← hv]
    simp [map_sum, map_smul, ContinuousLinearMap.smulRight_apply]
  rw [hrep]
  refine Finset.stronglyMeasurable_fun_sum (f := fun i a =>
    (EuclideanSpace.proj i : Eu d →L[ℝ] ℝ).smulRight (g a (EuclideanSpace.single i 1))) Finset.univ (fun i _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℝ (Eu d) F (EuclideanSpace.proj i)).continuous.comp_stronglyMeasurable (hg _)

lemma opNorm3_le {T : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v w z : Eu d, |T v w z| ≤ B * ‖v‖ * ‖w‖ * ‖z‖) : ‖T‖ ≤ B :=
  ContinuousLinearMap.opNorm_le_bound _ hB fun v =>
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg v)) fun w =>
      ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hB (norm_nonneg v)) (norm_nonneg w)) fun z => by
        rw [Real.norm_eq_abs]; exact h v w z

lemma khyp_of_plain {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
    {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
    {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
    {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
    {A c : ℝ}
    (hK : 0 ≤ A ∧ 0 < c ∧ MeasurableSet (S) ∧ Convex ℝ (S) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Eu d, HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Eu d, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Eu d, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ∀ v w z : Eu d,
        |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ x : Eu d, MeasureTheory.StronglyMeasurable (fun p : ℝ × Eu d => K p.1 x p.2)) ∧
      (∀ x : Eu d, MeasureTheory.StronglyMeasurable (fun p : ℝ × Eu d => K1 p.1 x p.2)) ∧
      (∀ x : Eu d, MeasureTheory.StronglyMeasurable (fun p : ℝ × Eu d => K2 p.1 x p.2)) ∧
      (∀ x v w z : Eu d, MeasureTheory.StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2 v w z)) ∧
      (∀ t : ℝ, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, MeasureTheory.IntegrableOn F (S) ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ (S), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧
          ∀ v w z : Eu d, |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Eu d, HasDerivAt (fun t => K t x y)
        ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
      (∀ t : ℝ, 0 < t → ∀ x : Eu d, ∫ y in (S), K t x y = 1)) :
    KHyp d S K K1 K2 K3 A c := by
  obtain ⟨hA, hc, hS, hconv, d1, d2, d3, b0, b1, b2, b3, m0, m1, m2, m3, dom, heat, mass⟩ := hK
  refine ⟨hA, hc, hS, hconv, d1, d2, d3, b0, b1, b2, fun t ht x hx y hy => opNorm3_le
    (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg ht.le _)) (G_pos (mul_pos hc ht) (x - y)).le)
    (b3 t ht x hx y hy), m0, m1, m2, fun x => sm_of_apply fun v => sm_of_apply fun w => sm_of_apply fun z =>
    m3 x v w z, fun t ht x₀ => ?_, heat, mass⟩
  obtain ⟨r, hr, F, hF, hb⟩ := dom t ht x₀
  refine ⟨r, hr, F, hF, fun x hx y hy => ⟨(hb x hx y hy).1, (hb x hx y hy).2.1, (hb x hx y hy).2.2.1, ?_⟩⟩
  exact opNorm3_le ((abs_nonneg _).trans (hb x hx y hy).1) (hb x hx y hy).2.2.2

/-- Resolvent-level transfer of a kernel-level linear condition on `K1`. -/
lemma tu1_bc_gen {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
    {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
    {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
    {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
    {A c : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (h : Eu d → ℝ) (lam : ℝ) {x v : Eu d}
    (hv : ∀ t : ℝ, 0 < t → ∀ y ∈ S, K1 t x y v = 0) : tu1 S K1 h lam x v = 0 := by
  unfold tu1
  refine clm_integral_zero (ContinuousLinearMap.apply ℝ ℝ v)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  rw [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hk : kw1 S K1 h t x v = 0 := by
    unfold kw1
    exact clm_integral_zero (ContinuousLinearMap.apply ℝ ℝ v)
      ((ae_restrict_iff' KH.hS).mpr (Eventually.of_forall fun y hy => by
        rw [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, hv t ht y hy, smul_zero]))
  rw [hk, mul_zero]

theorem ks_main (d : ℕ) (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ)
    (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ))
    (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (A c μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hK : 0 ≤ A ∧ 0 < c ∧ MeasurableSet (S) ∧ Convex ℝ (S) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Eu d, HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Eu d, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Eu d, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ∀ v w z : Eu d,
        |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ x : Eu d, MeasureTheory.StronglyMeasurable (fun p : ℝ × Eu d => K p.1 x p.2)) ∧
      (∀ x : Eu d, MeasureTheory.StronglyMeasurable (fun p : ℝ × Eu d => K1 p.1 x p.2)) ∧
      (∀ x : Eu d, MeasureTheory.StronglyMeasurable (fun p : ℝ × Eu d => K2 p.1 x p.2)) ∧
      (∀ x v w z : Eu d, MeasureTheory.StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2 v w z)) ∧
      (∀ t : ℝ, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, MeasureTheory.IntegrableOn F (S) ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ (S), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧
          ∀ v w z : Eu d, |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Eu d, HasDerivAt (fun t => K t x y)
        ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
      (∀ t : ℝ, 0 < t → ∀ x : Eu d, ∫ y in (S), K t x y = 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ h : Eu d → ℝ,
    (∃ Hh : ℝ, ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
    (∃ M0 : ℝ, ∀ y ∈ S, |h y| ≤ M0) →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ (x : Eu d) (r : ℝ), 0 < r → Metric.ball x r ⊆ S →
        HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ S, lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
          = h x) ∧
      (∀ x v : Eu d, (∀ t : ℝ, 0 < t → ∀ y ∈ S, K1 t x y v = 0) → u1 x v = 0) ∧
      ∀ M0 Hh : ℝ, 0 ≤ M0 → 0 ≤ Hh → (∀ y ∈ S, |h y| ≤ M0) →
        (∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
      (∀ x ∈ S, ∀ v w : Eu d,
        |u x| ≤ C * M0 * (1 / lam) ∧
        |u1 x v| ≤ C * M0 * (1 / lam) ^ (1 / 2 : ℝ) * ‖v‖ ∧
        |u2 x v w| ≤ C * Hh * (1 / lam) ^ (μ / 2) * ‖v‖ * ‖w‖) ∧
      (∀ x ∈ S, ∀ x' ∈ S, ∀ v w : Eu d,
        |u x - u x'| ≤ C * M0 * (1 / lam) ^ (1 - μ / 2) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * M0 * (1 / lam) ^ ((1 - μ) / 2) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * Hh * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖) := by
  have KH := khyp_of_plain hK
  have hA : 0 ≤ A := KH.hA
  have hc : 0 < c := KH.hc
  have hg1 : 0 < Real.Gamma 1 := Real.Gamma_pos_of_pos one_pos
  have hg2 : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hg3 : 0 < Real.Gamma (μ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hg4 : 0 < Real.Gamma (1 - μ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hg5 : 0 < Real.Gamma ((1 - μ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hgm : 0 < gm d := gm_pos d
  have hq : 0 < 2 / (μ / 2) + 1 / (1 / 2 - μ / 2) := by
    have : 0 < 1 / 2 - μ / 2 := by linarith
    positivity
  set k0 := A * Real.Gamma 1 with hk0
  set k1 := A * Real.Gamma (1 / 2) with hk1
  set k2 := A * gm d * c ^ (μ / 2) * Real.Gamma (μ / 2) with hk2
  set k3 := (2 * A) ^ (1 - μ) * A ^ μ * Real.Gamma (1 - μ / 2) with hk3
  set k4 := (2 * A) ^ (1 - μ) * A ^ μ * Real.Gamma ((1 - μ) / 2) with hk4
  set k5 := A * gm d * c ^ (μ / 2) * (2 / (μ / 2) + 1 / (1 / 2 - μ / 2)) with hk5
  have h0 : 0 ≤ k0 := by positivity
  have h1 : 0 ≤ k1 := by positivity
  have h2 : 0 ≤ k2 := by positivity
  have h3 : 0 ≤ k3 := by positivity
  have h4 : 0 ≤ k4 := by positivity
  have h5 : 0 ≤ k5 := by positivity
  refine ⟨k0 + k1 + k2 + k3 + k4 + k5, by positivity, ?_⟩
  intro lam hlam h ⟨Hh', hhol0⟩ ⟨M0', hsup0⟩
  have hhol'' : ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ max Hh' 0 * ‖y - z‖ ^ μ := fun y hy z hz =>
    (hhol0 y hy z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hH' : HolderOnS S μ (max M0' 0) (max Hh' 0) h :=
    ⟨le_max_right _ _, le_max_right _ _, fun y hy => (hsup0 y hy).trans (le_max_left _ _), hhol''⟩
  have hm : AEStronglyMeasurable h (volume.restrict S) :=
    (continuousOn_of_holder hμ0 hhol'').aestronglyMeasurable KH.hS
  have hl : 0 ≤ 1 / lam := by positivity
  refine ⟨tu0 S K h lam, tu1 S K1 h lam, tu2 S K2 h lam,
    fun x r hr hball => ⟨KH.hasFDerivAt_tu0 hH' hm hlam hr hball,
      KH.hasFDerivAt_tu1 hH' hm hμ0 (by linarith) hlam hr hball⟩,
    fun x hx => KH.equation hH' hm hμ0 (by linarith) hlam hx,
    fun x v hv => tu1_bc_gen KH h lam hv, ?_⟩
  intro M0 Hh hM0 hHh hsup hhol
  have hhol' : ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ := hhol
  have hH : HolderOnS S μ M0 Hh h := ⟨hM0, hHh, hsup, hhol'⟩
  refine ⟨?_, ?_⟩
  · intro x hx v w
    have s0 := (KH.tu0_sup hH hm hlam hx).2
    have s1 := (KH.tu1_sup hH hm hlam hx).2
    have s2 := (KH.tu2_sup hH hm hμ0 (by linarith) hlam hx).2
    rw [Real.norm_eq_abs, rpow_one] at s0
    refine ⟨?_, ?_, ?_⟩
    · exact (fin_bound (k := k0) (C := k0 + k1 + k2 + k3 + k4 + k5) (X := M0 * (1 / lam)) s0 (by rw [hk0]; ring) (by linarith) (by positivity)).trans_eq
        (by ring)
    · exact (fin_bound (k := k1) (C := k0 + k1 + k2 + k3 + k4 + k5) (X := M0 * (1 / lam) ^ (1 / 2 : ℝ) * ‖v‖)
        ((abs_app_le _ v).trans (mul_le_mul_of_nonneg_right s1 (norm_nonneg v))) (by rw [hk1]; ring)
        (by linarith) (by positivity)).trans_eq (by ring)
    · exact (fin_bound (k := k2) (C := k0 + k1 + k2 + k3 + k4 + k5) (X := Hh * (1 / lam) ^ (μ / 2) * ‖v‖ * ‖w‖)
        ((abs_app2_le _ v w).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right s2 (norm_nonneg v)) (norm_nonneg w))) (by rw [hk2]; ring)
        (by linarith) (by positivity)).trans_eq (by ring)
  · intro x hx x' hx' v w
    have s0 := KH.tu0_hol hH hm hμ0.le hμ1.le hlam hx hx'
    have s1 := KH.tu1_hol hH hm hμ0.le hμ1 hlam hx hx'
    have s2 := KH.tu2_hol hH hm hμ0 hμ1 hlam hx hx'
    rw [Real.norm_eq_abs] at s0
    have hsp := rpow_split (μ := μ) (by positivity : (0 : ℝ) ≤ 2 * A) hA hM0
    refine ⟨?_, ?_, ?_⟩
    · refine (fin_bound (k := k3) (C := k0 + k1 + k2 + k3 + k4 + k5) (X := M0 * (1 / lam) ^ (1 - μ / 2) * ‖x - x'‖ ^ μ) s0 ?_
        (by linarith) (by positivity)).trans_eq (by ring)
      rw [hsp, hk3]; ring
    · have e1 : tu1 S K1 h lam x v - tu1 S K1 h lam x' v
          = (tu1 S K1 h lam x - tu1 S K1 h lam x') v := by
        rw [sub_apply]
      rw [e1]
      refine (fin_bound (k := k4) (C := k0 + k1 + k2 + k3 + k4 + k5) (X := M0 * (1 / lam) ^ ((1 - μ) / 2) * ‖x - x'‖ ^ μ * ‖v‖)
        ((abs_app_le _ v).trans (mul_le_mul_of_nonneg_right s1 (norm_nonneg v))) ?_
        (by linarith) (by positivity)).trans_eq (by ring)
      rw [hsp, hk4]; ring
    · have e2 : tu2 S K2 h lam x v w - tu2 S K2 h lam x' v w
          = (tu2 S K2 h lam x - tu2 S K2 h lam x') v w := by
        rw [sub_apply, sub_apply]
      rw [e2]
      exact (fin_bound (k := k5) (C := k0 + k1 + k2 + k3 + k4 + k5) (X := Hh * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)
        ((abs_app2_le _ v w).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right s2 (norm_nonneg v)) (norm_nonneg w))) (by rw [hk5]; ring)
        (by linarith) (by positivity)).trans_eq (by ring)

end KSMain

end ObliqueLib

theorem solution (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (A c μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hK : 0 ≤ A ∧ 0 < c ∧ MeasurableSet (S) ∧ Convex ℝ (S) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ∀ v w z : EuclideanSpace ℝ (Fin d),
        |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K p.1 x p.2)) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K1 p.1 x p.2)) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K2 p.1 x p.2)) ∧
      (∀ x v w z : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K3 p.1 x p.2 v w z)) ∧
      (∀ t : ℝ, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.IntegrableOn F (S) ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ (S), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧
          ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasDerivAt (fun t => K t x y)
        ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
      (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), ∫ y in (S), K t x y = 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ h : EuclideanSpace ℝ (Fin d) → ℝ,
    (∃ Hh : ℝ, ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
    (∃ M0 : ℝ, ∀ y ∈ S, |h y| ≤ M0) →
    ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r → Metric.ball x r ⊆ S →
        HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ S, lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
          = h x) ∧
      (∀ x v : EuclideanSpace ℝ (Fin d), (∀ t : ℝ, 0 < t → ∀ y ∈ S, K1 t x y v = 0) → u1 x v = 0) ∧
      ∀ M0 Hh : ℝ, 0 ≤ M0 → 0 ≤ Hh → (∀ y ∈ S, |h y| ≤ M0) →
        (∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
      (∀ x ∈ S, ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x| ≤ C * M0 * (1 / lam) ∧
        |u1 x v| ≤ C * M0 * (1 / lam) ^ (1 / 2 : ℝ) * ‖v‖ ∧
        |u2 x v w| ≤ C * Hh * (1 / lam) ^ (μ / 2) * ‖v‖ * ‖w‖) ∧
      (∀ x ∈ S, ∀ x' ∈ S, ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x - u x'| ≤ C * M0 * (1 / lam) ^ (1 - μ / 2) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * M0 * (1 / lam) ^ ((1 - μ) / 2) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * Hh * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖) := by
  exact ObliqueLib.ks_main d S K K1 K2 K3 A c μ hμ0 hμ1 hK
