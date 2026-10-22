-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_tangential_hessian_low_energy_tail
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T13:37:19.725775+00:00
-- url     : https://prove2.me/submissions/4a1928ed-605f-4433-ba2f-1e61a457ac36

import Mathlib
import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_smoothAt_of_secondCollisionFree

/-!
# Positive tangential Hessian on the very-negative-energy tail

For every `0 < μ < 1` and `c ≥ 32` the full Hessian of the Levi-Civita Hamiltonian is
positive definite along the left energy component, hence so is its restriction to
tangent vectors.

1. *Barrier.* On the sphere `|z|² = 1/16` we have `K > 0` once `c ≥ 12`. The component is
   preconnected, contains the collision point (`z = 0`) and lies in `{K = 0}`, so by the
   intermediate value theorem it lies in `|z|² < 1/16`.
2. *Momentum bound.* `K = 0` and `|z|² < 1/16` give `|w|² ≤ 4`.
3. *Hessian.* With these bounds, `Hess K = diag(2c, 2c, 1, 1) + E` where the `w`-block of `E`
   vanishes, its mixed entries are `≤ 3/2` and its `z`-block entries are `≤ 14`
   (using `r = √D ≥ 7/8` in the explicit formula `kHess`). For `c ≥ 32` the quadratic form is
   `≥ 22 |v_z|² + |v_w|²/2`.
-/

namespace BirkhoffGlobalSection.LowEnergyTail

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian

theorem abs_mul_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- `D = |2z² - 1|² ≥ (1 - 2|z|²)²`. -/
theorem sec_ge (s : Phase) : (1 - 2 * zNormSq s) ^ 2 ≤ secondCollisionDistanceSq s := by
  unfold secondCollisionDistanceSq zNormSq
  nlinarith [sq_nonneg (s 1)]

theorem sqrt_sec_ge {s : Phase} (hZ : zNormSq s ≤ 1 / 16) :
    7 / 8 ≤ Real.sqrt (secondCollisionDistanceSq s) := by
  have hZ0 : 0 ≤ zNormSq s := by unfold zNormSq; positivity
  have h : (7 / 8 : ℝ) ^ 2 ≤ secondCollisionDistanceSq s := by
    have := sec_ge s
    nlinarith
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (by norm_num)] at this

/-- The `μ |z|² / √D` term is at most `1/14` when `|z|² ≤ 1/16`. -/
theorem sing_le {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) {s : Phase} (hZ : zNormSq s ≤ 1 / 16) :
    μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s) ≤ 1 / 14 := by
  have hr := sqrt_sec_ge hZ
  have hZ0 : 0 ≤ zNormSq s := by unfold zNormSq; positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul hμ1.le hZ hZ0 (by norm_num)]

/-- Cauchy--Schwarz for the two bilinear terms of `K`. -/
theorem cs_a (s : Phase) : (s 0 * s 3 - s 1 * s 2) ^ 2 ≤ zNormSq s * wNormSq s := by
  unfold zNormSq wNormSq; nlinarith [sq_nonneg (s 0 * s 2 + s 1 * s 3)]

theorem cs_b (s : Phase) : (s 0 * s 3 + s 1 * s 2) ^ 2 ≤ zNormSq s * wNormSq s := by
  unfold zNormSq wNormSq; nlinarith [sq_nonneg (s 0 * s 2 - s 1 * s 3)]

/-- **Barrier.** `K > 0` on the sphere `|z|² = 1/16` once `c ≥ 12`. -/
theorem barrier {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : 12 ≤ c) {s : Phase}
    (hZ : zNormSq s = 1 / 16) : 0 < leviCivitaHamiltonian μ c s := by
  have ht := sing_le hμ0 hμ1 hZ.le
  have ha := cs_a s
  have hb := cs_b s
  have hW : 0 ≤ wNormSq s := by unfold wNormSq; positivity
  set a := s 0 * s 3 - s 1 * s 2
  set b := s 0 * s 3 + s 1 * s 2
  have hK : leviCivitaHamiltonian μ c s = wNormSq s / 2 + c * zNormSq s - (1 - μ) / 2
      + 2 * zNormSq s * a - μ * b
      - μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s) := by
    unfold leviCivitaHamiltonian; ring
  rw [hK, hZ]; rw [hZ] at ha hb ht
  nlinarith [sq_nonneg (a + 1 / 16), sq_nonneg (2 * b - 1 / 4),
    mul_nonneg hμ0.le (sq_nonneg (2 * b - 1 / 4)),
    mul_nonneg (sub_nonneg.mpr hμ1.le) (by positivity : (0 : ℝ) ≤ 4 * b ^ 2 + 1 / 16)]

theorem leftEnergyComponent_subset (μ c : ℝ) :
    leftEnergyComponent μ c ⊆ regularEnergyLocus μ c :=
  connectedComponentIn_subset _ _

theorem zNormSq_leftCollisionPoint (μ : ℝ) : zNormSq (leftCollisionPoint μ) = 0 := by
  simp [zNormSq, leftCollisionPoint]

theorem continuous_zNormSq' : Continuous zNormSq := by unfold zNormSq; fun_prop

/-- **Confinement.** The component lies in `|z|² < 1/16` once `c ≥ 12`. -/
theorem confine {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : 12 ≤ c) :
    ∀ s ∈ leftEnergyComponent μ c, zNormSq s < 1 / 16 := by
  intro s hs
  by_contra hlt
  push Not at hlt
  have hne : (leftEnergyComponent μ c).Nonempty := ⟨s, hs⟩
  have hbase : leftCollisionPoint μ ∈ leftEnergyComponent μ c :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.mp hne)
  have hpre : IsPreconnected (leftEnergyComponent μ c) := isPreconnected_connectedComponentIn
  have hiv := hpre.intermediate_value hbase hs continuous_zNormSq'.continuousOn
  rw [zNormSq_leftCollisionPoint] at hiv
  obtain ⟨s', hs', hz'⟩ := hiv ⟨by norm_num, hlt⟩
  have hK := (leftEnergyComponent_subset μ c hs').1
  have := barrier hμ0 hμ1 hc hz'
  linarith

/-- **Momentum bound** on the component. -/
theorem wbound {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : 12 ≤ c) :
    ∀ s ∈ leftEnergyComponent μ c, wNormSq s ≤ 4 := by
  intro s hs
  have hZ := confine hμ0 hμ1 hc s hs
  have hK := (leftEnergyComponent_subset μ c hs).1
  have ht := sing_le hμ0 hμ1 hZ.le
  have ha := cs_a s
  have hb := cs_b s
  have hW : 0 ≤ wNormSq s := by unfold wNormSq; positivity
  have hZ0 : 0 ≤ zNormSq s := by unfold zNormSq; positivity
  have ht0 : 0 ≤ μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s) := by positivity
  set a := s 0 * s 3 - s 1 * s 2
  set b := s 0 * s 3 + s 1 * s 2
  have hK' : leviCivitaHamiltonian μ c s = wNormSq s / 2 + c * zNormSq s - (1 - μ) / 2
      + 2 * zNormSq s * a - μ * b
      - μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s) := by
    unfold leviCivitaHamiltonian; ring
  rw [hK'] at hK
  have hZW : zNormSq s * wNormSq s ≤ wNormSq s / 16 := by nlinarith
  nlinarith [mul_nonneg hZ0 (sq_nonneg (a + 1)), mul_le_mul_of_nonneg_right hZ.le (sq_nonneg a),
    mul_nonneg hμ0.le (sq_nonneg (2 * b - 1 / 4)),
    mul_nonneg (sub_nonneg.mpr hμ1.le) (by positivity : (0 : ℝ) ≤ 4 * b ^ 2 + 1 / 16),
    mul_nonneg (by linarith : (0 : ℝ) ≤ c) hZ0, mul_nonneg (by linarith : (0 : ℝ) ≤ c - 12) hZ0]

/-! ## The Hessian -/

/-- Bound for the singular part of an entry of `kHessR`. -/
theorem corr_le {μ r Z hz a1 a2 b1 b2 h : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hr : 7 / 8 ≤ r)
    (hZ0 : 0 ≤ Z) (hZ : Z ≤ 1 / 16) (hhz : |hz| ≤ 2) (ha1 : |a1| ≤ 1 / 2) (ha2 : |a2| ≤ 1 / 2)
    (hb1 : |b1| ≤ 9 / 4) (hb2 : |b2| ≤ 9 / 4) (hh : |h| ≤ 11) :
    |μ * (hz / r - (a1 * b2 + a2 * b1) / (2 * r ^ 3) - Z * h / (2 * r ^ 3)
      + 3 * Z * b1 * b2 / (4 * r ^ 5))| ≤ 6 := by
  have hr0 : 0 < r := by linarith
  set i := r⁻¹ with hi
  have hi0 : 0 ≤ i := inv_nonneg.mpr hr0.le
  have hi1 : i ≤ 8 / 7 := by
    rw [hi]; rw [inv_le_comm₀ hr0 (by norm_num)]; linarith
  have e : hz / r - (a1 * b2 + a2 * b1) / (2 * r ^ 3) - Z * h / (2 * r ^ 3)
      + 3 * Z * b1 * b2 / (4 * r ^ 5) =
      hz * i - (a1 * b2 + a2 * b1) * i ^ 3 / 2 - Z * h * i ^ 3 / 2
        + 3 * Z * b1 * b2 * i ^ 5 / 4 := by
    rw [hi]; field_simp
  rw [e]
  have hi' : |i| ≤ 8 / 7 := by rw [abs_of_nonneg hi0]; exact hi1
  have hi3 : |i ^ 3| ≤ (8 / 7) ^ 3 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hi' 3
  have hi5 : |i ^ 5| ≤ (8 / 7) ^ 5 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hi' 5
  have hZ' : |Z| ≤ 1 / 16 := by rw [abs_of_nonneg hZ0]; exact hZ
  have t1 := abs_mul_le' hhz hi'
  have t2a := abs_mul_le' (abs_mul_le' ha1 hb2) hi3
  have t2b := abs_mul_le' (abs_mul_le' ha2 hb1) hi3
  have t3 := abs_mul_le' (abs_mul_le' hZ' hh) hi3
  have t4 := abs_mul_le' (abs_mul_le' (abs_mul_le' hZ' hb1) hb2) hi5
  have hμ' : |μ| ≤ 1 := by rw [abs_of_nonneg hμ0]; exact hμ1
  refine (abs_mul_le' hμ' (abs_le.mpr ⟨?_, ?_⟩ : |_| ≤ (6 : ℝ))).trans (by norm_num)
  · obtain ⟨_, _⟩ := abs_le.mp t1; obtain ⟨_, _⟩ := abs_le.mp t2a
    obtain ⟨_, _⟩ := abs_le.mp t2b; obtain ⟨_, _⟩ := abs_le.mp t3
    obtain ⟨_, _⟩ := abs_le.mp t4
    nlinarith
  · obtain ⟨_, _⟩ := abs_le.mp t1; obtain ⟨_, _⟩ := abs_le.mp t2a
    obtain ⟨_, _⟩ := abs_le.mp t2b; obtain ⟨_, _⟩ := abs_le.mp t3
    obtain ⟨_, _⟩ := abs_le.mp t4
    nlinarith

section entries

variable {s : Phase} (hz16 : zNormSq s ≤ 1 / 16) (hW : wNormSq s ≤ 4)
include hz16

theorem bx : |s 0| ≤ 1 / 4 := by
  unfold zNormSq at hz16
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (s 1)], by nlinarith [sq_nonneg (s 1)]⟩

theorem by' : |s 1| ≤ 1 / 4 := by
  unfold zNormSq at hz16
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (s 0)], by nlinarith [sq_nonneg (s 0)]⟩

theorem bdZ (k : Fin 4) : |dZ s k| ≤ 1 / 2 := by
  obtain ⟨hx, hx'⟩ := abs_le.mp (bx hz16); obtain ⟨hy, hy'⟩ := abs_le.mp (by' hz16)
  refine abs_le.mpr ⟨?_, ?_⟩ <;> fin_cases k <;> simp [dZ] <;> linarith

theorem bdD (k : Fin 4) : |dD s k| ≤ 9 / 4 := by
  have hx := bx hz16; have hy := by' hz16
  have hZ0 : 0 ≤ zNormSq s := by unfold zNormSq; positivity
  fin_cases k
  · show |dD s 0| ≤ 9 / 4
    have e : dD s 0 = 8 * s 0 * (2 * zNormSq s - 1) := by simp [dD, zNormSq]; ring
    rw [e]
    have h1 : |2 * zNormSq s - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := abs_mul_le' (abs_mul_le' (by norm_num : |(8 : ℝ)| ≤ 8) hx) h1; linarith
  · show |dD s 1| ≤ 9 / 4
    have e : dD s 1 = 8 * s 1 * (2 * zNormSq s + 1) := by simp [dD, zNormSq]; ring
    rw [e]
    have h1 : |2 * zNormSq s + 1| ≤ 9 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := abs_mul_le' (abs_mul_le' (by norm_num : |(8 : ℝ)| ≤ 8) hy) h1; linarith
  · norm_num [dD]
  · norm_num [dD]

theorem bhD (k l : Fin 4) : |hD s k l| ≤ 11 := by
  have hz := hz16
  unfold zNormSq at hz
  have hxy : |s 0 * s 1| ≤ 1 / 32 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (s 0 + s 1), sq_nonneg (s 0 - s 1)]
  obtain ⟨hxy1, hxy2⟩ := abs_le.mp hxy
  have h0 := sq_nonneg (s 0); have h1 := sq_nonneg (s 1)
  refine abs_le.mpr ⟨?_, ?_⟩ <;> fin_cases k <;> fin_cases l <;> simp [hD] <;> nlinarith

omit hz16 in
theorem bhZ (k l : Fin 4) : |hZ k l| ≤ 2 := by
  fin_cases k <;> fin_cases l <;> simp [hZ]

theorem corr_entry {μ c : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (k l : Fin 4) :
    |kHess μ c s k l - hP μ c s k l| ≤ 6 := by
  have hZ0 : 0 ≤ zNormSq s := by unfold zNormSq; positivity
  have h := corr_le hμ0 hμ1 (sqrt_sec_ge hz16) hZ0 hz16 (bhZ k l) (bdZ hz16 k) (bdZ hz16 l)
    (bdD hz16 k) (bdD hz16 l) (bhD hz16 k l)
  have e : kHess μ c s k l - hP μ c s k l = -(μ * (hZ k l / rD s
      - (dZ s k * dD s l + dZ s l * dD s k) / (2 * rD s ^ 3)
      - zNormSq s * hD s k l / (2 * rD s ^ 3)
      + 3 * zNormSq s * dD s k * dD s l / (4 * rD s ^ 5))) := by
    simp only [kHess, kHessR]; ring
  rw [e, abs_neg]; exact h

end entries

/-- Pure algebra: the perturbed `diag(2c, 2c, 1, 1)` form is positive. -/
theorem quad_pos {c A00 e01 A11 m02 m03 m12 m13 a b p q : ℝ} (hc : 32 ≤ c)
    (h00 : |A00 - 2 * c| ≤ 14) (h01 : |e01| ≤ 10) (h11 : |A11 - 2 * c| ≤ 14)
    (g02 : |m02| ≤ 3 / 2) (g03 : |m03| ≤ 3 / 2) (g12 : |m12| ≤ 3 / 2) (g13 : |m13| ≤ 3 / 2)
    (hv : a ≠ 0 ∨ b ≠ 0 ∨ p ≠ 0 ∨ q ≠ 0) :
    0 < A00 * a ^ 2 + 2 * e01 * a * b + A11 * b ^ 2
      + 2 * (m02 * a * p + m03 * a * q + m12 * b * p + m13 * b * q) + p ^ 2 + q ^ 2 := by
  obtain ⟨k00, k00'⟩ := abs_le.mp h00; obtain ⟨k01, k01'⟩ := abs_le.mp h01
  obtain ⟨k11, k11'⟩ := abs_le.mp h11
  have s02 : m02 ^ 2 ≤ 9 / 4 := by nlinarith [abs_le.mp g02]
  have s03 : m03 ^ 2 ≤ 9 / 4 := by nlinarith [abs_le.mp g03]
  have s12 : m12 ^ 2 ≤ 9 / 4 := by nlinarith [abs_le.mp g12]
  have s13 : m13 ^ 2 ≤ 9 / 4 := by nlinarith [abs_le.mp g13]
  have lb : 22 * (a ^ 2 + b ^ 2) + (p ^ 2 + q ^ 2) / 2 ≤
      A00 * a ^ 2 + 2 * e01 * a * b + A11 * b ^ 2
        + 2 * (m02 * a * p + m03 * a * q + m12 * b * p + m13 * b * q) + p ^ 2 + q ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A00 - 2 * c + 14) (sq_nonneg a),
      mul_nonneg (by linarith : (0 : ℝ) ≤ A11 - 2 * c + 14) (sq_nonneg b),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 10 + e01) (sq_nonneg (a + b)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 10 - e01) (sq_nonneg (a - b)),
      sq_nonneg (2 * m02 * a + p / 2), sq_nonneg (2 * m03 * a + q / 2),
      sq_nonneg (2 * m12 * b + p / 2), sq_nonneg (2 * m13 * b + q / 2),
      mul_le_mul_of_nonneg_right s02 (sq_nonneg a), mul_le_mul_of_nonneg_right s03 (sq_nonneg a),
      mul_le_mul_of_nonneg_right s12 (sq_nonneg b), mul_le_mul_of_nonneg_right s13 (sq_nonneg b),
      mul_nonneg (by linarith : (0 : ℝ) ≤ c - 32) (sq_nonneg a),
      mul_nonneg (by linarith : (0 : ℝ) ≤ c - 32) (sq_nonneg b)]
  refine lt_of_lt_of_le ?_ lb
  rcases hv with h | h | h | h
  · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; positivity
  · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; positivity
  · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; positivity
  · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; positivity

/-- Linear-in-each-factor bound for the polynomial part of the `z`-block. -/
theorem lin2 {u v w z : ℝ} (A B : ℝ) (hu : |u| ≤ 2) (hv : |v| ≤ 1 / 4) (hw : |w| ≤ 2)
    (hz : |z| ≤ 1 / 4) : |A * u * v + B * w * z| ≤ (|A| + |B|) / 2 := by
  have h1 := abs_mul_le' (abs_mul_le' (le_refl |A|) hu) hv
  have h2 := abs_mul_le' (abs_mul_le' (le_refl |B|) hw) hz
  calc |A * u * v + B * w * z| ≤ |A * u * v| + |B * w * z| := abs_add_le _ _
    _ ≤ (|A| + |B|) / 2 := by linarith

theorem kHess_w {μ c : ℝ} (s : Phase) (k l : Fin 4) (h : 2 ≤ k.val ∨ 2 ≤ l.val) :
    kHess μ c s k l = hP μ c s k l := by
  simp only [kHess, kHessR]
  fin_cases k <;> fin_cases l <;> simp at h ⊢ <;> simp [hZ, hD, dZ, dD]

theorem kHess_symm (μ c : ℝ) (s : Phase) (k l : Fin 4) : kHess μ c s k l = kHess μ c s l k := by
  have h1 : hP μ c s k l = hP μ c s l k := by fin_cases k <;> fin_cases l <;> simp [hP]
  have h2 : hZ k l = hZ l k := by fin_cases k <;> fin_cases l <;> simp [hZ]
  have h3 : hD s k l = hD s l k := by fin_cases k <;> fin_cases l <;> simp [hD]
  simp only [kHess, kHessR]
  rw [h1, h2, h3]; ring

theorem expand4 (H : Matrix (Fin 4) (Fin 4) ℝ) (v : Phase) (hs : ∀ k l, H k l = H l k)
    (h22 : H 2 2 = 1) (h33 : H 3 3 = 1) (h23 : H 2 3 = 0) :
    ∑ k, ∑ l, v k * v l * H k l =
      H 0 0 * v 0 ^ 2 + 2 * H 0 1 * v 0 * v 1 + H 1 1 * v 1 ^ 2
        + 2 * (H 0 2 * v 0 * v 2 + H 0 3 * v 0 * v 3 + H 1 2 * v 1 * v 2 + H 1 3 * v 1 * v 3)
        + v 2 ^ 2 + v 3 ^ 2 := by
  simp only [Fin.sum_univ_four]
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2, h22, h33, h23]
  ring

/-- **Hessian positivity** under the a priori bounds. -/
theorem hess_pos {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : 32 ≤ c) {s : Phase}
    (hz16 : zNormSq s ≤ 1 / 16) (hW : wNormSq s ≤ 4) (v : Phase) (hv : v ≠ 0) :
    0 < ∑ k, ∑ l, v k * v l * kHess μ c s k l := by
  have hx := bx hz16; have hy := by' hz16
  have hp : |s 2| ≤ 2 := by
    unfold wNormSq at hW
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (s 3)], by nlinarith [sq_nonneg (s 3)]⟩
  have hq : |s 3| ≤ 2 := by
    unfold wNormSq at hW
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (s 2)], by nlinarith [sq_nonneg (s 2)]⟩
  have C00 := corr_entry hz16 (c := c) hμ0.le hμ1.le 0 0
  have C01 := corr_entry hz16 (c := c) hμ0.le hμ1.le 0 1
  have C11 := corr_entry hz16 (c := c) hμ0.le hμ1.le 1 1
  have p00 : hP μ c s 0 0 - 2 * c = -4 * s 2 * s 1 + 12 * s 3 * s 0 := by simp [hP]; ring
  have p01 : hP μ c s 0 1 = -4 * s 2 * s 0 + 4 * s 3 * s 1 := by simp [hP]
  have p11 : hP μ c s 1 1 - 2 * c = -12 * s 2 * s 1 + 4 * s 3 * s 0 := by simp [hP]; ring
  have L00 := lin2 (-4) 12 hp hy hq hx
  have L01 := lin2 (-4) 4 hp hx hq hy
  have L11 := lin2 (-12) 4 hp hy hq hx
  rw [← p00] at L00; rw [← p01] at L01; rw [← p11] at L11
  norm_num at L00 L01 L11
  have e00 : |kHess μ c s 0 0 - 2 * c| ≤ 14 := by
    have := abs_add_le (kHess μ c s 0 0 - hP μ c s 0 0) (hP μ c s 0 0 - 2 * c)
    rw [show kHess μ c s 0 0 - hP μ c s 0 0 + (hP μ c s 0 0 - 2 * c)
      = kHess μ c s 0 0 - 2 * c by ring] at this
    linarith
  have e01 : |kHess μ c s 0 1| ≤ 10 := by
    have := abs_add_le (kHess μ c s 0 1 - hP μ c s 0 1) (hP μ c s 0 1)
    rw [show kHess μ c s 0 1 - hP μ c s 0 1 + hP μ c s 0 1 = kHess μ c s 0 1 by ring] at this
    linarith
  have e11 : |kHess μ c s 1 1 - 2 * c| ≤ 14 := by
    have := abs_add_le (kHess μ c s 1 1 - hP μ c s 1 1) (hP μ c s 1 1 - 2 * c)
    rw [show kHess μ c s 1 1 - hP μ c s 1 1 + (hP μ c s 1 1 - 2 * c)
      = kHess μ c s 1 1 - 2 * c by ring] at this
    linarith
  have hz := hz16; unfold zNormSq at hz
  have hxy : |s 0 * s 1| ≤ 1 / 32 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (s 0 + s 1), sq_nonneg (s 0 - s 1)]
  have h0 := sq_nonneg (s 0); have h1 := sq_nonneg (s 1)
  have g02 : |kHess μ c s 0 2| ≤ 3 / 2 := by
    rw [kHess_w s 0 2 (by decide)]
    have e : hP μ c s 0 2 = -4 * (s 0 * s 1) := by simp [hP]; ring
    rw [e]; have := abs_mul_le' (by norm_num : |(-4 : ℝ)| ≤ 4) hxy; linarith
  have g03 : |kHess μ c s 0 3| ≤ 3 / 2 := by
    rw [kHess_w s 0 3 (by decide)]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> simp [hP] <;> nlinarith
  have g12 : |kHess μ c s 1 2| ≤ 3 / 2 := by
    rw [kHess_w s 1 2 (by decide)]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> simp [hP] <;> nlinarith
  have g13 : |kHess μ c s 1 3| ≤ 3 / 2 := by
    rw [kHess_w s 1 3 (by decide)]
    have e : hP μ c s 1 3 = 4 * (s 0 * s 1) := by simp [hP]; ring
    rw [e]; have := abs_mul_le' (by norm_num : |(4 : ℝ)| ≤ 4) hxy; linarith
  have w22 : kHess μ c s 2 2 = 1 := by rw [kHess_w s 2 2 (by decide)]; simp [hP]
  have w33 : kHess μ c s 3 3 = 1 := by rw [kHess_w s 3 3 (by decide)]; simp [hP]
  have w23 : kHess μ c s 2 3 = 0 := by rw [kHess_w s 2 3 (by decide)]; simp [hP]
  rw [expand4 _ v (kHess_symm μ c s) w22 w33 w23]
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2])
  exact quad_pos hc e00 e01 e11 g02 g03 g12 g13 hv'

end BirkhoffGlobalSection.LowEnergyTail

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian
  BirkhoffGlobalSection.LowEnergyTail in
theorem solution :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        HasPositiveTangentialHessianOn (leviCivitaHamiltonian μ c)
          (leftEnergyComponent μ c) := by
  refine ⟨1, 32, one_pos, fun μ c hμ0 hμ1 _ hc _ => ?_⟩
  have hc12 : (12 : ℝ) ≤ c := by linarith
  have hU : ∀ s ∈ leftEnergyComponent μ c, s ∈ U := fun s hs =>
    (leftEnergyComponent_subset μ c hs).2
  refine ⟨fun s hs => ?_, fun s hs v hv _ => ?_⟩
  · exact (leviCivita_smoothAt_of_secondCollisionFree μ c s (hU s hs)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · rw [(leviCivita_explicit_derivatives μ c).2.1 s (hU s hs) v v]
    exact hess_pos hμ0 hμ1 hc (confine hμ0 hμ1 hc12 s hs).le (wbound hμ0 hμ1 hc12 s hs) v hv
