-- Prove2me | solution 1 for FreedmanTail.theorem_4_1_freedman_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T14:56:21.912734+00:00
-- url     : https://prove2.me/submissions/0e310e14-e5d7-42b8-9ea3-2bed8a1e7c2f

import Mathlib
import Definitions.Def_FreedmanTail_partialSum
import Definitions.Def_FreedmanTail_varSum

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace FreedmanAux

/-! ## Part S: scalar lemmas -/

/-- `log (1 - u) ≤ -u - u²/2` for `0 ≤ u < 1` (first two terms of `-log(1-u) = Σ u^k/k`). -/
lemma log_one_sub_le (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) : Real.log (1 - u) ≤ -u - u ^ 2 / 2 := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := u) (by rw [abs_of_nonneg h0]; exact h1)
  have h := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs
  simp [Finset.sum_range_succ] at h
  linarith

/-- The second conjunct of Freedman's (4.1). -/
lemma freedman_arith (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by
  have hab : 0 < a + b := by linarith
  have hq : 0 < b / (a + b) := div_pos hb hab
  rw [Real.rpow_def_of_pos hq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hbq : b / (a + b) = 1 - a / (a + b) := by field_simp; ring
  have hu0 : 0 ≤ a / (a + b) := by positivity
  have hu1 : a / (a + b) < 1 := by rw [div_lt_one hab]; linarith
  have hl := log_one_sub_le (a / (a + b)) hu0 hu1
  rw [hbq]
  have hua : a / (a + b) * (a + b) = a := by field_simp
  have hr : -(a ^ 2) / (2 * (a + b)) = -((a / (a + b)) ^ 2 / 2) * (a + b) := by
    field_simp
  rw [hr]
  have hm := mul_le_mul_of_nonneg_right hl hab.le
  nlinarith [hm, hua]

lemma one_le_exp_mul_quad (w : ℝ) (hw : 0 ≤ w) : 1 ≤ Real.exp w * (1 - w + w ^ 2 / 2) := by
  let g : ℝ → ℝ := fun w => Real.exp w * (1 - w + w ^ 2 / 2)
  have hd : ∀ x, HasDerivAt g (Real.exp x * (x ^ 2 / 2)) x := by
    intro x
    have h1 := Real.hasDerivAt_exp x
    have h2 : HasDerivAt (fun w : ℝ => 1 - w + w ^ 2 / 2) (-1 + x) x := by
      refine (((hasDerivAt_id x).const_sub 1).add ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv ?_
      norm_num
    exact (h1.mul h2).congr_deriv (by ring)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x _
      rw [(hd x).deriv]
      positivity
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hw) hw
  simpa [g] using h

lemma exp_le_quad_neg (z : ℝ) (hz : z ≤ 0) : Real.exp z ≤ 1 + z + z ^ 2 / 2 := by
  have h := one_le_exp_mul_quad (-z) (by linarith)
  have hpos := Real.exp_pos z
  have he : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp z = Real.exp z * 1 := by ring
    _ ≤ Real.exp z * (Real.exp (-z) * (1 - -z + (-z) ^ 2 / 2)) := by gcongr
    _ = 1 + z + z ^ 2 / 2 := by rw [← mul_assoc, he]; ring

lemma hasSum_exp_tail (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (n + 2) / ((n + 2).factorial : ℝ)) (Real.exp x - 1 - x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  have e : Real.exp x - ∑ i ∈ Finset.range 2, x ^ i / (i.factorial : ℝ) = Real.exp x - 1 - x := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, div_one]
    ring
  rw [e] at h2
  exact h2

lemma exp_le_quad_pos (c z : ℝ) (hc : 0 < c) (hz0 : 0 ≤ z) (hz : z ≤ c) :
    Real.exp z - 1 - z ≤ (Real.exp c - 1 - c) / c ^ 2 * z ^ 2 := by
  have key : HasSum (fun n : ℕ => (z ^ 2 / c ^ 2) * (c ^ (n + 2) / ((n + 2).factorial : ℝ)))
      ((z ^ 2 / c ^ 2) * (Real.exp c - 1 - c)) := (hasSum_exp_tail c).mul_left _
  have hle := hasSum_le (fun n => ?_) (hasSum_exp_tail z) key
  · calc _ ≤ _ := hle
      _ = _ := by ring
  · have hf : (0 : ℝ) < ((n + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hcn : (0 : ℝ) < c ^ 2 := by positivity
    rw [show z ^ 2 / c ^ 2 * (c ^ (n + 2) / ((n + 2).factorial : ℝ))
        = (z ^ 2 * c ^ n) / ((n + 2).factorial : ℝ) by field_simp; ring]
    apply div_le_div_of_nonneg_right _ hf.le
    have hp := pow_le_pow_left₀ hz0 hz n
    rw [pow_add]
    nlinarith [sq_nonneg z, hp]

/-- Bennett's quadratic bound: `e^z ≤ 1 + z + φ(c) z²` for `z ≤ c`, `φ(c) = (e^c-1-c)/c²`. -/
lemma exp_le_quad (c z : ℝ) (hc : 0 < c) (hz : z ≤ c) :
    Real.exp z ≤ 1 + z + (Real.exp c - 1 - c) / c ^ 2 * z ^ 2 := by
  rcases le_total z 0 with h | h
  · have h1 := exp_le_quad_neg z h
    have hq := Real.quadratic_le_exp_of_nonneg hc.le
    have hphi : (1 : ℝ) / 2 ≤ (Real.exp c - 1 - c) / c ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have := mul_le_mul_of_nonneg_right hphi (sq_nonneg z)
    linarith
  · have := exp_le_quad_pos c z hc h hz
    linarith


/-! ## Part P: pull-out property for the conditional Lebesgue expectation -/

lemma lintegral_mul_condLExp {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {h f : Ω → ℝ≥0∞} (hh : Measurable[m] h)
    (hf : Measurable[mΩ] f) :
    ∫⁻ ω, h ω * f ω ∂μ = ∫⁻ ω, h ω * μ⁻[f|m] ω ∂μ := by
  have hC : Measurable[mΩ] (μ⁻[f|m]) := measurable_condLExp' m μ f
  have htrim : (μ.withDensity f).trim hm = (μ.withDensity (μ⁻[f|m])).trim hm := by
    apply @Measure.ext Ω m
    intro s hs
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs),
      withDensity_apply _ (hm s hs), setLIntegral_condLExp hm μ f hs]
  have h1 := lintegral_withDensity_eq_lintegral_mul μ hf (hh.mono hm le_rfl)
  have h2 := lintegral_withDensity_eq_lintegral_mul μ hC (hh.mono hm le_rfl)
  have h3 := lintegral_trim hm (μ := μ.withDensity f) hh
  have h4 := lintegral_trim hm (μ := μ.withDensity (μ⁻[f|m])) hh
  simp only [Pi.mul_apply] at h1 h2
  calc ∫⁻ ω, h ω * f ω ∂μ = ∫⁻ ω, f ω * h ω ∂μ := by simp_rw [mul_comm]
    _ = ∫⁻ ω, h ω ∂((μ.withDensity f).trim hm) := by rw [h3, h1]
    _ = ∫⁻ ω, h ω ∂((μ.withDensity (μ⁻[f|m])).trim hm) := by rw [htrim]
    _ = _ := by rw [h4, h2]; simp_rw [mul_comm]

lemma condLExp_mul_left {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {h f : Ω → ℝ≥0∞} (hh : Measurable[m] h)
    (hf : Measurable[mΩ] f) :
    μ⁻[fun ω => h ω * f ω|m] =ᵐ[μ] fun ω => h ω * μ⁻[f|m] ω := by
  refine (ae_eq_condLExp hm μ _ (hh.mul (measurable_condLExp m μ f)) (fun s hs => ?_)).symm
  rw [← lintegral_indicator (hm s hs), ← lintegral_indicator (hm s hs)]
  have := lintegral_mul_condLExp hm (μ := μ) (hh.indicator hs) hf
  have e1 : s.indicator (h * μ⁻[f|m]) = fun ω => s.indicator h ω * μ⁻[f|m] ω := by
    ext ω; by_cases hω : ω ∈ s <;> simp [hω]
  have e2 : s.indicator (fun ω => h ω * f ω) = fun ω => s.indicator h ω * f ω := by
    ext ω; by_cases hω : ω ∈ s <;> simp [hω]
  rw [e1, e2]; exact this.symm

/-- Conditional expectation of a pointwise quadratic bound with `m`-measurable coefficients. -/
lemma cond_poly {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    {φ α β γ : Ω → ℝ≥0∞} (hφ : Measurable[mΩ] φ) (hα : Measurable[m] α) (hβ : Measurable[m] β)
    (hγ : Measurable[m] γ)
    (hpt : ∀ᵐ ω ∂μ, φ ω + β ω * ENNReal.ofReal (-X ω)
      ≤ α ω + β ω * ENNReal.ofReal (X ω) + γ ω * ENNReal.ofReal (X ω ^ 2)) :
    ∀ᵐ ω ∂μ, μ⁻[φ|m] ω + β ω * μ⁻[fun ω => ENNReal.ofReal (-X ω)|m] ω
      ≤ α ω + β ω * μ⁻[fun ω => ENNReal.ofReal (X ω)|m] ω
        + γ ω * μ⁻[fun ω => ENNReal.ofReal (X ω ^ 2)|m] ω := by
  have hneg : Measurable[mΩ] (fun ω => ENNReal.ofReal (-X ω)) := hX.neg.ennreal_ofReal
  have hpos : Measurable[mΩ] (fun ω => ENNReal.ofReal (X ω)) := hX.ennreal_ofReal
  have hsq : Measurable[mΩ] (fun ω => ENNReal.ofReal (X ω ^ 2)) := (hX.pow_const 2).ennreal_ofReal
  have hα' : Measurable[mΩ] α := hα.mono hm le_rfl
  have hβ' : Measurable[mΩ] β := hβ.mono hm le_rfl
  have L : ∀ᵐ ω ∂μ, μ⁻[fun ω => φ ω + β ω * ENNReal.ofReal (-X ω)|m] ω
      = μ⁻[φ|m] ω + μ⁻[fun ω => β ω * ENNReal.ofReal (-X ω)|m] ω :=
    condLExp_add_left _ hφ.aemeasurable
  have L2 := condLExp_mul_left hm (μ := μ) hβ hneg
  have R1 : ∀ᵐ ω ∂μ, μ⁻[fun ω => α ω + β ω * ENNReal.ofReal (X ω)
        + γ ω * ENNReal.ofReal (X ω ^ 2)|m] ω
      = μ⁻[fun ω => α ω + β ω * ENNReal.ofReal (X ω)|m] ω
        + μ⁻[fun ω => γ ω * ENNReal.ofReal (X ω ^ 2)|m] ω :=
    condLExp_add_left _ (hα'.add (hβ'.mul hpos)).aemeasurable
  have R2 : ∀ᵐ ω ∂μ, μ⁻[fun ω => α ω + β ω * ENNReal.ofReal (X ω)|m] ω
      = μ⁻[α|m] ω + μ⁻[fun ω => β ω * ENNReal.ofReal (X ω)|m] ω :=
    condLExp_add_left _ hα'.aemeasurable
  have R3 := condLExp_mul_left hm (μ := μ) hβ hpos
  have R4 := condLExp_mul_left hm (μ := μ) hγ hsq
  have Rα : μ⁻[α|m] = α := condLExp_eq_self hm μ hα
  have mono := condLExp_mono (mΩ := m) hpt
  filter_upwards [L, L2, R1, R2, R3, R4, mono] with ω hL hL2 hR1 hR2 hR3 hR4 hmo
  calc μ⁻[φ|m] ω + β ω * μ⁻[fun ω => ENNReal.ofReal (-X ω)|m] ω
        = μ⁻[fun ω => φ ω + β ω * ENNReal.ofReal (-X ω)|m] ω := by rw [hL, hL2]
    _ ≤ μ⁻[fun ω => α ω + β ω * ENNReal.ofReal (X ω) + γ ω * ENNReal.ofReal (X ω ^ 2)|m] ω := hmo
    _ = _ := by rw [hR1, hR2, hR3, hR4, Rα]

/-! ## Part C (scalar): the two-point bound -/

/-- `G l c = (e^{lc} - 1 - lc)/c²`. -/
noncomputable def Gc (l c : ℝ) : ℝ := (Real.exp (l * c) - 1 - l * c) / c ^ 2

lemma Gc_nonneg (l c : ℝ) : 0 ≤ Gc l c := by
  unfold Gc
  apply div_nonneg _ (sq_nonneg c)
  linarith [Real.add_one_le_exp (l * c)]

/-- Pointwise quadratic majorant of `e^{lx}` touching at `y` and at `1`. -/
lemma ptwise_quad (l y x : ℝ) (hl : 0 < l) (hy : y ≤ 0) (hx : x ≤ 1) :
    Real.exp (l * x) ≤ Real.exp (l * y) * (1 + l * (x - y) + Gc l (1 - y) * (x - y) ^ 2) := by
  have hc : 0 < l * (1 - y) := by have : 0 < 1 - y := by linarith
                                  positivity
  have hq := exp_le_quad (l * (1 - y)) (l * (x - y)) hc (by nlinarith)
  have e1 : (Real.exp (l * (1 - y)) - 1 - l * (1 - y)) / (l * (1 - y)) ^ 2 * (l * (x - y)) ^ 2
      = Gc l (1 - y) * (x - y) ^ 2 := by
    unfold Gc
    have h1 : (1 - y) ≠ 0 := by linarith
    have h2 : l ≠ 0 := hl.ne'
    field_simp
  rw [e1] at hq
  calc Real.exp (l * x) = Real.exp (l * y) * Real.exp (l * (x - y)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le

/-- Scalar chain: the quadratic's mean under (mean `1-d`, variance `u d`) is at most
`exp(e(l) · u d)`. Here `y = 1 - d - u`. -/
lemma scalar_chain (l d u : ℝ) (hl : 0 < l) (hd : 1 ≤ d) (hu : 0 ≤ u) :
    Real.exp (l * (1 - d - u)) * (1 + l * u + Gc l (d + u) * (u ^ 2 + u * d))
      ≤ Real.exp ((Real.exp l - 1 - l) * (u * d)) := by
  have hd0 : 0 < d := by linarith
  have hc : 0 < d + u := by linarith
  have hE : Real.exp (l * (1 - d - u)) * Real.exp (l * (d + u)) = Real.exp l := by
    rw [← Real.exp_add]; congr 1; ring
  have hid : Real.exp (l * (1 - d - u)) * (1 + l * u + Gc l (d + u) * (u ^ 2 + u * d))
      = u / (d + u) * Real.exp l + d / (d + u) * Real.exp (l * (1 - d - u)) := by
    rw [← hE]; unfold Gc; field_simp; ring
  have ht : Real.exp (l * (1 - d - u)) ≤ Real.exp (l * (-u / d)) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hl.le
    rw [le_div_iff₀ hd0]; nlinarith
  have hz : l * (-u / d) ≤ l := by
    have : -u / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd0.le
    nlinarith
  have hq := exp_le_quad l (l * (-u / d)) hl hz
  have he : 0 ≤ Real.exp l - 1 - l := by linarith [Real.add_one_le_exp l]
  have h1 : d / (d + u) * Real.exp (l * (-u / d)) ≤ d / (d + u) *
      (1 + l * (-u / d) + (Real.exp l - 1 - l) / l ^ 2 * (l * (-u / d)) ^ 2) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have h2 : u / (d + u) * Real.exp l + d / (d + u) *
      (1 + l * (-u / d) + (Real.exp l - 1 - l) / l ^ 2 * (l * (-u / d)) ^ 2)
      = 1 + (Real.exp l - 1 - l) * (u / d) := by
    have : l ≠ 0 := hl.ne'
    field_simp; ring
  have h3 : (Real.exp l - 1 - l) * (u / d) ≤ (Real.exp l - 1 - l) * (u * d) :=
    mul_le_mul_of_nonneg_left ((div_le_self hu hd).trans (le_mul_of_one_le_right hu hd)) he
  have h4 := Real.add_one_le_exp ((Real.exp l - 1 - l) * (u / d))
  have h5 : Real.exp ((Real.exp l - 1 - l) * (u / d)) ≤ Real.exp ((Real.exp l - 1 - l) * (u * d)) :=
    Real.exp_le_exp.mpr h3
  have h6 : d / (d + u) * Real.exp (l * (1 - d - u)) ≤ d / (d + u) * Real.exp (l * (-u / d)) :=
    mul_le_mul_of_nonneg_left ht (by positivity)
  rw [hid]
  linarith


/-! ## Part C: the conditional MGF bound -/

/-- `Eneg e v = exp(-e v)` for finite `v`, and `0` at `v = ∞`. -/
noncomputable def Eneg (e : ℝ) (v : ℝ≥0∞) : ℝ≥0∞ :=
  if v = ∞ then 0 else ENNReal.ofReal (Real.exp (-(e * v.toReal)))

noncomputable def Acoef (l y : ℝ) : ℝ := Real.exp (l * y) * (1 - l * y + Gc l (1 - y) * y ^ 2)
noncomputable def Bcoef (l y : ℝ) : ℝ := Real.exp (l * y) * (l - 2 * Gc l (1 - y) * y)
noncomputable def Ccoef (l y : ℝ) : ℝ := Real.exp (l * y) * Gc l (1 - y)

lemma measurable_Gc (l : ℝ) : Measurable (fun c => Gc l c) := by
  unfold Gc; fun_prop

lemma measurable_Acoef (l : ℝ) : Measurable (Acoef l) := by
  have := (measurable_Gc l).comp (measurable_const.sub measurable_id : Measurable fun y : ℝ => 1 - y)
  unfold Acoef; fun_prop

lemma measurable_Bcoef (l : ℝ) : Measurable (Bcoef l) := by
  have := (measurable_Gc l).comp (measurable_const.sub measurable_id : Measurable fun y : ℝ => 1 - y)
  unfold Bcoef; fun_prop

lemma measurable_Ccoef (l : ℝ) : Measurable (Ccoef l) := by
  have := (measurable_Gc l).comp (measurable_const.sub measurable_id : Measurable fun y : ℝ => 1 - y)
  unfold Ccoef; fun_prop

lemma ptwise_enn (l y x : ℝ) (hl : 0 < l) (hy : y ≤ 0) (hx : x ≤ 1) :
    ENNReal.ofReal (Real.exp (l * x)) + ENNReal.ofReal (Bcoef l y) * ENNReal.ofReal (-x)
      ≤ ENNReal.ofReal (Acoef l y) + ENNReal.ofReal (Bcoef l y) * ENNReal.ofReal x
        + ENNReal.ofReal (Ccoef l y) * ENNReal.ofReal (x ^ 2) := by
  have hq := ptwise_quad l y x hl hy hx
  have hG := Gc_nonneg l (1 - y)
  have hE := Real.exp_pos (l * y)
  have hly : 0 ≤ l * -y := mul_nonneg hl.le (by linarith)
  have hA : 0 ≤ Acoef l y := by
    unfold Acoef; apply mul_nonneg hE.le; nlinarith [mul_nonneg hG (sq_nonneg y)]
  have hB : 0 ≤ Bcoef l y := by
    unfold Bcoef; apply mul_nonneg hE.le; nlinarith [mul_nonneg hG (neg_nonneg.mpr hy)]
  have hC : 0 ≤ Ccoef l y := mul_nonneg hE.le hG
  have key : Real.exp (l * x) ≤ Acoef l y + Bcoef l y * x + Ccoef l y * x ^ 2 := by
    calc _ ≤ _ := hq
      _ = _ := by unfold Acoef Bcoef Ccoef; ring
  rcases le_total 0 x with h0 | h0
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -x ≤ 0), mul_zero, add_zero,
      ← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_add hA (mul_nonneg hB h0),
      ← ENNReal.ofReal_add (add_nonneg hA (mul_nonneg hB h0)) (mul_nonneg hC (sq_nonneg x))]
    exact ENNReal.ofReal_le_ofReal key
  · rw [ENNReal.ofReal_of_nonpos h0, mul_zero, add_zero, ← ENNReal.ofReal_mul hB,
      ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_add (Real.exp_pos _).le (mul_nonneg hB (by linarith)),
      ← ENNReal.ofReal_add hA (mul_nonneg hC (sq_nonneg x))]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [key])

lemma jensen_enn (m0 x : ℝ) :
    (0 : ℝ≥0∞) + ENNReal.ofReal (-2 * m0) * ENNReal.ofReal (-x)
      ≤ ENNReal.ofReal (m0 ^ 2) + ENNReal.ofReal (-2 * m0) * ENNReal.ofReal x
        + ENNReal.ofReal 1 * ENNReal.ofReal (x ^ 2) := by
  rcases le_total 0 m0 with hm0 | hm0
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -2 * m0 ≤ 0)]; simp
  rcases le_total 0 x with h0 | h0
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -x ≤ 0)]; simp
  · rw [ENNReal.ofReal_of_nonpos h0, mul_zero, add_zero, zero_add, ENNReal.ofReal_one, one_mul,
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - m0)])

lemma enn_real (K P Q S : ℝ≥0∞) (a b g : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hP : P ≠ ∞) (hQ : Q ≠ ∞) (hS : S ≠ ∞)
    (h : K + ENNReal.ofReal b * Q ≤ ENNReal.ofReal a + ENNReal.ofReal b * P + ENNReal.ofReal g * S) :
    K ≠ ∞ ∧ K.toReal + b * Q.toReal ≤ a + b * P.toReal + g * S.toReal := by
  have h1 : ENNReal.ofReal a + ENNReal.ofReal b * P ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP⟩
  have h2 : ENNReal.ofReal g * S ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS
  have hR : ENNReal.ofReal a + ENNReal.ofReal b * P + ENNReal.ofReal g * S ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨h1, h2⟩
  have hK : K ≠ ∞ := ne_top_of_le_ne_top hR (le_trans le_self_add h)
  have hQ' : ENNReal.ofReal b * Q ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQ
  have := ENNReal.toReal_mono hR h
  rw [ENNReal.toReal_add hK hQ', ENNReal.toReal_add h1 h2,
    ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP)] at this
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
    ENNReal.toReal_ofReal hg] at this
  exact ⟨hK, this⟩

set_option maxHeartbeats 1000000 in
/-- Step C: `E{e^{lX} | m} · exp(-e(l) Var{X | m}) ≤ 1` a.e. -/
lemma cond_mgf {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ 1)
    (hdrift : μ⁻[fun ω => ENNReal.ofReal (X ω)|m] ≤ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (-X ω)|m])
    {l : ℝ} (hl : 0 < l) :
    ∀ᵐ ω ∂μ, μ⁻[fun ω => ENNReal.ofReal (Real.exp (l * X ω))|m] ω
      * Eneg (Real.exp l - 1 - l) (FreedmanTail.condVarE m μ X ω) ≤ 1 := by
  have hmeasP : Measurable[m] (fun ω => (μ⁻[fun ω => ENNReal.ofReal (X ω)|m] ω).toReal) :=
    (measurable_condLExp m μ _).ennreal_toReal
  have hmeasQ : Measurable[m] (fun ω => (μ⁻[fun ω => ENNReal.ofReal (-X ω)|m] ω).toReal) :=
    (measurable_condLExp m μ _).ennreal_toReal
  have hmeasS : Measurable[m] (fun ω => (μ⁻[fun ω => ENNReal.ofReal (X ω ^ 2)|m] ω).toReal) :=
    (measurable_condLExp m μ _).ennreal_toReal
  obtain ⟨mr, hmr⟩ : ∃ f : Ω → ℝ, f = fun ω => (μ⁻[fun ω => ENNReal.ofReal (X ω)|m] ω).toReal
      - (μ⁻[fun ω => ENNReal.ofReal (-X ω)|m] ω).toReal := ⟨_, rfl⟩
  obtain ⟨Vr, hVr⟩ : ∃ f : Ω → ℝ, f = fun ω =>
      (μ⁻[fun ω => ENNReal.ofReal (X ω ^ 2)|m] ω).toReal - mr ω ^ 2 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ f : Ω → ℝ, f = fun ω => min (mr ω - Vr ω / (1 - mr ω)) 0 := ⟨_, rfl⟩
  have hmeas_mr : Measurable[m] mr := by rw [hmr]; exact hmeasP.sub hmeasQ
  have hmeas_Vr : Measurable[m] Vr := by rw [hVr]; exact hmeasS.sub (hmeas_mr.pow_const 2)
  have hmeas_y : Measurable[m] y := by
    rw [hy]; exact (hmeas_mr.sub (hmeas_Vr.div (measurable_const.sub hmeas_mr))).min measurable_const
  have hy0 : ∀ ω, y ω ≤ 0 := fun ω => by rw [hy]; exact min_le_right _ _
  have hφ : Measurable[mΩ] (fun ω => ENNReal.ofReal (Real.exp (l * X ω))) :=
    (Real.measurable_exp.comp (hX.const_mul l)).ennreal_ofReal
  -- the main conditional inequality
  have H5 := cond_poly hm (μ := μ) hX hφ ((measurable_Acoef l).comp hmeas_y).ennreal_ofReal
    ((measurable_Bcoef l).comp hmeas_y).ennreal_ofReal
    ((measurable_Ccoef l).comp hmeas_y).ennreal_ofReal
    (by filter_upwards [hle] with ω hω using ptwise_enn l (y ω) (X ω) hl (hy0 ω) hω)
  -- conditional Jensen
  have H4 := cond_poly hm (μ := μ) hX (φ := 0) (α := fun ω => ENNReal.ofReal (mr ω ^ 2))
    (β := fun ω => ENNReal.ofReal (-2 * mr ω)) (γ := fun _ => ENNReal.ofReal 1)
    measurable_const (hmeas_mr.pow_const 2).ennreal_ofReal
    (hmeas_mr.const_mul (-2)).ennreal_ofReal measurable_const
    (ae_of_all _ fun ω => jensen_enn (mr ω) (X ω))
  -- E{X⁻|m} ≤ (1 + 2 E{X⁺|m} + E{X²|m})/2
  have H3 := cond_poly hm (μ := μ) hX (φ := 0) (α := fun _ => ENNReal.ofReal ((-1) ^ 2))
    (β := fun _ => ENNReal.ofReal (-2 * -1)) (γ := fun _ => ENNReal.ofReal 1)
    measurable_const measurable_const measurable_const measurable_const
    (ae_of_all _ fun ω => jensen_enn (-1) (X ω))
  have H1 : μ⁻[fun ω => ENNReal.ofReal (X ω)|m] ≤ᵐ[μ] μ⁻[fun _ => (1 : ℝ≥0∞)|m] :=
    condLExp_mono (by filter_upwards [hle] with ω hω using ENNReal.ofReal_le_one.2 hω)
  rw [condLExp_const hm μ] at H1
  filter_upwards [H1, hdrift, H3, H4, H5] with ω h1 h2 h3 h4 h5
  have hmrω : mr ω = (μ⁻[fun ω => ENNReal.ofReal (X ω)|m] ω).toReal
      - (μ⁻[fun ω => ENNReal.ofReal (-X ω)|m] ω).toReal := by rw [hmr]
  have hVrω : Vr ω = (μ⁻[fun ω => ENNReal.ofReal (X ω ^ 2)|m] ω).toReal - mr ω ^ 2 := by rw [hVr]
  have hyω : y ω = min (mr ω - Vr ω / (1 - mr ω)) 0 := by rw [hy]
  set K := μ⁻[fun ω => ENNReal.ofReal (Real.exp (l * X ω))|m] ω with hK
  set P := μ⁻[fun ω => ENNReal.ofReal (X ω)|m] ω with hP
  set Q := μ⁻[fun ω => ENNReal.ofReal (-X ω)|m] ω with hQ
  set S := μ⁻[fun ω => ENNReal.ofReal (X ω ^ 2)|m] ω with hS
  by_cases hSt : S = ∞
  · have hV : FreedmanTail.condVarE m μ X ω = ∞ := by
      unfold FreedmanTail.condVarE
      rw [← hS, hSt]; exact ENNReal.top_sub ENNReal.ofReal_ne_top
    simp [Eneg, hV]
  have hPf : P ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top h1
  have hQf : Q ≠ ∞ := by
    have hR : ENNReal.ofReal ((-1) ^ 2) + ENNReal.ofReal (-2 * -1) * P + ENNReal.ofReal 1 * S ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPf⟩, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSt⟩
    have h2Q : ENNReal.ofReal (-2 * -1) * Q ≠ ∞ := ne_top_of_le_ne_top hR (le_trans le_add_self h3)
    refine ne_top_of_le_ne_top h2Q (le_mul_of_one_le_left (by positivity) ?_)
    rw [ENNReal.one_le_ofReal]; norm_num
  have hPQ : P.toReal ≤ Q.toReal := ENNReal.toReal_mono hQf h2
  have hmr0 : mr ω ≤ 0 := by rw [hmrω]; linarith
  obtain ⟨-, h4r⟩ := enn_real _ P Q S (mr ω ^ 2) (-2 * mr ω) 1 (sq_nonneg _) (by linarith)
    zero_le_one hPf hQf hSt h4
  have hK0 : 0 ≤ (μ⁻[(0 : Ω → ℝ≥0∞)|m] ω).toReal := ENNReal.toReal_nonneg
  have hVr0 : 0 ≤ Vr ω := by rw [hVrω]; nlinarith [h4r, hmrω]
  set d := 1 - mr ω with hd
  have hd1 : 1 ≤ d := by linarith
  set u := Vr ω / d with hu
  have hu0 : 0 ≤ u := div_nonneg hVr0 (by linarith)
  have hyω' : y ω = 1 - d - u := by
    rw [hyω, min_eq_left (by linarith)]; ring
  obtain ⟨hKf, h5r⟩ := enn_real K P Q S (Acoef l (y ω)) (Bcoef l (y ω)) (Ccoef l (y ω))
    (by have := ptwise_enn l (y ω) 0 hl (hy0 ω) zero_le_one
        unfold Acoef; apply mul_nonneg (Real.exp_pos _).le
        have hG := Gc_nonneg l (1 - y ω)
        nlinarith [mul_nonneg hl.le (neg_nonneg.mpr (hy0 ω)), mul_nonneg hG (sq_nonneg (y ω))])
    (by unfold Bcoef; apply mul_nonneg (Real.exp_pos _).le
        have hG := Gc_nonneg l (1 - y ω)
        nlinarith [mul_nonneg hG (neg_nonneg.mpr (hy0 ω))])
    (mul_nonneg (Real.exp_pos _).le (Gc_nonneg _ _)) hPf hQf hSt h5
  have hVud : Vr ω = u * d := by rw [hu]; field_simp
  have hSr : S.toReal = u * d + (1 - d) ^ 2 := by
    have := hVrω; rw [hVud] at this; rw [← hd] at *; nlinarith [this]
  have hPQr : P.toReal - Q.toReal = 1 - d := by rw [hd, hmrω]; ring
  have hG : Gc l (1 - (1 - d - u)) = Gc l (d + u) := by congr 1; ring
  have hsum : Acoef l (y ω) + Bcoef l (y ω) * P.toReal + Ccoef l (y ω) * S.toReal
      - Bcoef l (y ω) * Q.toReal
      = Real.exp (l * (1 - d - u)) * (1 + l * u + Gc l (d + u) * (u ^ 2 + u * d)) := by
    rw [show Bcoef l (y ω) * P.toReal = Bcoef l (y ω) * Q.toReal + Bcoef l (y ω) * (1 - d) by
      rw [← hPQr]; ring, hSr, hyω']
    unfold Acoef Bcoef Ccoef; rw [hG]; ring
  have hsc := scalar_chain l d u hl hd1 hu0
  have hKr : K.toReal ≤ Real.exp ((Real.exp l - 1 - l) * Vr ω) := by
    rw [hVud]; linarith
  have hCV : FreedmanTail.condVarE m μ X ω = ENNReal.ofReal (Vr ω) := by
    unfold FreedmanTail.condVarE
    rw [← hS, ← hP, ← hQ, ← ENNReal.ofReal_toReal hSt, ← hmrω, ← ENNReal.ofReal_sub _ (sq_nonneg _),
      hVrω]
  rw [hCV, Eneg, if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hVr0,
    ← ENNReal.ofReal_toReal hKf, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_one]
  calc K.toReal * Real.exp (-((Real.exp l - 1 - l) * Vr ω))
      ≤ Real.exp ((Real.exp l - 1 - l) * Vr ω) * Real.exp (-((Real.exp l - 1 - l) * Vr ω)) :=
        mul_le_mul_of_nonneg_right hKr (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp


/-! ## Part M: the exponential supermartingale -/

lemma Eneg_add (e : ℝ) (u v : ℝ≥0∞) : Eneg e (u + v) = Eneg e u * Eneg e v := by
  unfold Eneg
  by_cases hu : u = ∞
  · simp [hu]
  by_cases hv : v = ∞
  · simp [hv]
  rw [if_neg (ENNReal.add_ne_top.2 ⟨hu, hv⟩), if_neg hu, if_neg hv, ENNReal.toReal_add hu hv,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

lemma Eneg_zero (e : ℝ) : Eneg e 0 = 1 := by simp [Eneg]

lemma measurable_Eneg (e : ℝ) : Measurable (Eneg e) := by
  unfold Eneg
  exact Measurable.ite (measurableSet_singleton ∞) measurable_const (by fun_prop)

lemma measurable_condVarE {Ω : Type*} {mΩ : MeasurableSpace Ω} (m : MeasurableSpace Ω)
    (μ : Measure[mΩ] Ω) (Y : Ω → ℝ) : Measurable[m] (FreedmanTail.condVarE m μ Y) := by
  unfold FreedmanTail.condVarE
  have h1 := measurable_condLExp m μ (fun ω => ENNReal.ofReal (Y ω ^ 2))
  have h2 := (measurable_condLExp m μ (fun ω => ENNReal.ofReal (Y ω))).ennreal_toReal
  have h3 := (measurable_condLExp m μ (fun ω => ENNReal.ofReal (-Y ω))).ennreal_toReal
  exact h1.sub ((h2.sub h3).pow_const 2).ennreal_ofReal

/-- `Z_n = exp(l S_n - e(l) T_n)` (with `exp(-∞) = 0`). -/
noncomputable def Zp {Ω : Type*} {mΩ : MeasurableSpace Ω} (F : Filtration ℕ mΩ) (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (l * FreedmanTail.partialSum X n ω))
    * Eneg (Real.exp l - 1 - l) (FreedmanTail.varSum F μ X n ω)

lemma Zp_succ {Ω : Type*} {mΩ : MeasurableSpace Ω} (F : Filtration ℕ mΩ) (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) (ω : Ω) :
    Zp F μ X l (n + 1) ω = Zp F μ X l n ω * (ENNReal.ofReal (Real.exp (l * X n ω))
      * Eneg (Real.exp l - 1 - l) (FreedmanTail.condVarE (F n) μ (X n) ω)) := by
  unfold Zp FreedmanTail.partialSum FreedmanTail.varSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Eneg_add, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

lemma Zp_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} (F : Filtration ℕ mΩ) (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) : Zp F μ X l 0 ω = 1 := by
  simp [Zp, FreedmanTail.partialSum, FreedmanTail.varSum, Eneg_zero]

lemma measurable_Zp {Ω : Type*} {mΩ : MeasurableSpace Ω} (F : Filtration ℕ mΩ) (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (l : ℝ) (hX : ∀ k, Measurable[F (k + 1)] (X k)) (n : ℕ) :
    Measurable[F n] (Zp F μ X l n) := by
  unfold Zp FreedmanTail.partialSum FreedmanTail.varSum
  have hS : Measurable[F n] (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
    Finset.measurable_sum _ (fun i hi => (hX i).mono (F.mono (Finset.mem_range.mp hi)) le_rfl)
  have hT : Measurable[F n]
      (fun ω => ∑ i ∈ Finset.range n, FreedmanTail.condVarE (F i) μ (X i) ω) :=
    Finset.measurable_sum _ (fun i hi =>
      (measurable_condVarE (F i) μ (X i)).mono (F.mono (Finset.mem_range.mp hi).le) le_rfl)
  exact ((Real.measurable_exp.comp (hS.const_mul l)).ennreal_ofReal).mul
    ((measurable_Eneg _).comp hT)

lemma supermart_step {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ 1)
    (hdrift : μ⁻[fun ω => ENNReal.ofReal (X ω)|m] ≤ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (-X ω)|m])
    {l : ℝ} (hl : 0 < l) {h : Ω → ℝ≥0∞} (hh : Measurable[m] h) {A : Set Ω}
    (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, h ω * (ENNReal.ofReal (Real.exp (l * X ω))
      * Eneg (Real.exp l - 1 - l) (FreedmanTail.condVarE m μ X ω)) ∂μ ≤ ∫⁻ ω in A, h ω ∂μ := by
  have hE : Measurable[m] (fun ω => Eneg (Real.exp l - 1 - l) (FreedmanTail.condVarE m μ X ω)) :=
    (measurable_Eneg _).comp (measurable_condVarE m μ X)
  have hφ : Measurable[mΩ] (fun ω => ENNReal.ofReal (Real.exp (l * X ω))) :=
    (Real.measurable_exp.comp (hX.const_mul l)).ennreal_ofReal
  rw [← lintegral_indicator (hm A hA), ← lintegral_indicator (hm A hA)]
  have hH : Measurable[m] (A.indicator
      (fun ω => h ω * Eneg (Real.exp l - 1 - l) (FreedmanTail.condVarE m μ X ω))) :=
    (hh.mul hE).indicator hA
  have eq1 : A.indicator (fun ω => h ω * (ENNReal.ofReal (Real.exp (l * X ω))
      * Eneg (Real.exp l - 1 - l) (FreedmanTail.condVarE m μ X ω)))
      = fun ω => A.indicator (fun ω => h ω
          * Eneg (Real.exp l - 1 - l) (FreedmanTail.condVarE m μ X ω)) ω
          * ENNReal.ofReal (Real.exp (l * X ω)) := by
    ext ω; by_cases hω : ω ∈ A <;> simp [hω]; ring
  rw [eq1, lintegral_mul_condLExp hm hH hφ]
  apply lintegral_mono_ae
  filter_upwards [cond_mgf hm hX hle hdrift hl] with ω hω
  by_cases hωA : ω ∈ A
  · simp only [Set.indicator_of_mem hωA]
    calc _ = h ω * (μ⁻[fun ω => ENNReal.ofReal (Real.exp (l * X ω))|m] ω
          * Eneg (Real.exp l - 1 - l) (FreedmanTail.condVarE m μ X ω)) := by ring
      _ ≤ h ω * 1 := by gcongr
      _ = h ω := mul_one _
  · simp [hωA]

/-! ## Part O: maximal inequality for a nonnegative supermartingale -/

set_option maxHeartbeats 1000000 in
lemma maximal {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (Zs : ℕ → Ω → ℝ≥0∞) (hZm : ∀ n, Measurable[F n] (Zs n))
    (hstep : ∀ n (A : Set Ω), MeasurableSet[F n] A →
      ∫⁻ ω in A, Zs (n + 1) ω ∂μ ≤ ∫⁻ ω in A, Zs n ω ∂μ) (c : ℝ≥0∞) (N : ℕ) :
    c * μ {ω | ∃ k ≤ N, c ≤ Zs k ω} ≤ ∫⁻ ω, Zs 0 ω ∂μ := by
  have hG : ∀ N, MeasurableSet[F N] {ω | ∃ k ≤ N, c ≤ Zs k ω} := by
    intro N
    have : {ω | ∃ k ≤ N, c ≤ Zs k ω} = ⋃ k, ⋃ (_ : k ≤ N), {ω | c ≤ Zs k ω} := by ext; simp
    rw [this]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk =>
      measurableSet_le measurable_const ((hZm k).mono (F.mono hk) le_rfl)
  have split : ∀ (s : Set Ω), MeasurableSet s → ∀ f : Ω → ℝ≥0∞,
      ∫⁻ ω, (s.indicator (fun _ => c) ω + sᶜ.indicator f ω) ∂μ = c * μ s + ∫⁻ ω in sᶜ, f ω ∂μ := by
    intro s hs f
    rw [lintegral_add_left (measurable_const.indicator hs), lintegral_indicator hs,
      lintegral_indicator hs.compl, setLIntegral_const]
  have key : ∀ N, ∫⁻ ω, ({ω | ∃ k ≤ N, c ≤ Zs k ω}.indicator (fun _ => c) ω
      + {ω | ∃ k ≤ N, c ≤ Zs k ω}ᶜ.indicator (Zs N) ω) ∂μ ≤ ∫⁻ ω, Zs 0 ω ∂μ := by
    intro N
    induction N with
    | zero =>
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ {ω | ∃ k ≤ 0, c ≤ Zs k ω}
      · have hc : c ≤ Zs 0 ω := by
          obtain ⟨k, hk, hc⟩ := hω; rwa [Nat.le_zero.mp hk] at hc
        simp only [Set.indicator_apply, Set.mem_compl_iff, hω, not_true_eq_false, if_true,
          if_false, add_zero]
        exact hc
      · simp only [Set.indicator_apply, Set.mem_compl_iff, hω, not_false_eq_true, if_true,
          if_false, zero_add, le_refl]
    | succ N ih =>
      have hGN := hG N
      have hGN' : MeasurableSet {ω | ∃ k ≤ N, c ≤ Zs k ω} := F.le N _ hGN
      have hGN1' : MeasurableSet {ω | ∃ k ≤ N + 1, c ≤ Zs k ω} := F.le (N + 1) _ (hG (N + 1))
      calc _ ≤ ∫⁻ ω, ({ω | ∃ k ≤ N, c ≤ Zs k ω}.indicator (fun _ => c) ω
            + {ω | ∃ k ≤ N, c ≤ Zs k ω}ᶜ.indicator (Zs (N + 1)) ω) ∂μ := by
            apply lintegral_mono
            intro ω
            by_cases h1 : ω ∈ {ω | ∃ k ≤ N, c ≤ Zs k ω}
            · have h2 : ω ∈ {ω | ∃ k ≤ N + 1, c ≤ Zs k ω} := by
                obtain ⟨k, hk, hc⟩ := h1; exact ⟨k, by omega, hc⟩
              simp only [Set.indicator_apply, Set.mem_compl_iff, h1, h2, not_true_eq_false,
                if_true, if_false, le_refl]
            · by_cases h2 : ω ∈ {ω | ∃ k ≤ N + 1, c ≤ Zs k ω}
              · have hc : c ≤ Zs (N + 1) ω := by
                  obtain ⟨k, hk, hc⟩ := h2
                  rcases Nat.lt_or_ge k (N + 1) with h | h
                  · exact (h1 ⟨k, by omega, hc⟩).elim
                  · rwa [show k = N + 1 by omega] at hc
                simp only [Set.indicator_apply, Set.mem_compl_iff, h1, h2, not_true_eq_false,
                  not_false_eq_true, if_true, if_false, add_zero, zero_add]
                exact hc
              · simp only [Set.indicator_apply, Set.mem_compl_iff, h1, h2, not_false_eq_true,
                  if_true, if_false, zero_add, le_refl]
        _ = c * μ {ω | ∃ k ≤ N, c ≤ Zs k ω}
            + ∫⁻ ω in {ω | ∃ k ≤ N, c ≤ Zs k ω}ᶜ, Zs (N + 1) ω ∂μ := split _ hGN' _
        _ ≤ c * μ {ω | ∃ k ≤ N, c ≤ Zs k ω}
            + ∫⁻ ω in {ω | ∃ k ≤ N, c ≤ Zs k ω}ᶜ, Zs N ω ∂μ := by
            exact add_le_add le_rfl (hstep N _ hGN.compl)
        _ = _ := (split _ hGN' _).symm
        _ ≤ _ := ih
  have hGN' : MeasurableSet {ω | ∃ k ≤ N, c ≤ Zs k ω} := F.le N _ (hG N)
  refine le_trans ?_ (key N)
  rw [split _ hGN']
  exact le_self_add

end FreedmanAux

open MeasureTheory FreedmanTail in
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable[F (k + 1)] (X k))
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ 1)
    (hdrift : ∀ k, μ⁻[fun ω => ENNReal.ofReal (X k ω) | F k]
      ≤ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (- X k ω) | F k])
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    μ {ω | ∃ n, a ≤ partialSum X n ω ∧ varSum F μ X n ω ≤ ENNReal.ofReal b}
        ≤ ENNReal.ofReal ((b / (a + b)) ^ (a + b) * Real.exp a)
      ∧ (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by
  refine ⟨?_, FreedmanAux.freedman_arith a b ha hb⟩
  have hab : 0 < 1 + a / b := by have := div_pos ha hb; linarith
  obtain ⟨l, hl_def⟩ : ∃ l : ℝ, l = Real.log (1 + a / b) := ⟨_, rfl⟩
  have hl : 0 < l := by rw [hl_def]; exact Real.log_pos (by have := div_pos ha hb; linarith)
  have hel : Real.exp l = 1 + a / b := by rw [hl_def]; exact Real.exp_log hab
  obtain ⟨e, he_def⟩ : ∃ e : ℝ, e = Real.exp l - 1 - l := ⟨_, rfl⟩
  have he : 0 ≤ e := by rw [he_def]; linarith [Real.add_one_le_exp l]
  have hstep : ∀ n (A : Set Ω), MeasurableSet[F n] A →
      ∫⁻ ω in A, FreedmanAux.Zp F μ X l (n + 1) ω ∂μ ≤ ∫⁻ ω in A, FreedmanAux.Zp F μ X l n ω ∂μ :=
    fun n A hA => by
      simp_rw [FreedmanAux.Zp_succ]
      exact FreedmanAux.supermart_step (F.le n) ((hX n).mono (F.le (n + 1)) le_rfl) (hle n)
        (hdrift n) hl (FreedmanAux.measurable_Zp F μ X l hX n) hA
  have hZ0 : ∫⁻ ω, FreedmanAux.Zp F μ X l 0 ω ∂μ = 1 := by simp [FreedmanAux.Zp_zero]
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal (Real.exp (l * a) * Real.exp (-(e * b))) :=
    ⟨_, rfl⟩
  have hsub : {ω | ∃ n, a ≤ partialSum X n ω ∧ varSum F μ X n ω ≤ ENNReal.ofReal b}
      ⊆ ⋃ N, {ω | ∃ k ≤ N, c ≤ FreedmanAux.Zp F μ X l k ω} := by
    rintro ω ⟨n, hSn, hTn⟩
    refine Set.mem_iUnion.2 ⟨n, n, le_rfl, ?_⟩
    have hTf : varSum F μ X n ω ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTn
    have hTr : (varSum F μ X n ω).toReal ≤ b := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hTn
      rwa [ENNReal.toReal_ofReal hb.le] at this
    rw [hc_def, FreedmanAux.Zp, FreedmanAux.Eneg, if_neg hTf, ← he_def,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hSn hl.le))
      (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hTr he]))
      (Real.exp_pos _).le (Real.exp_pos _).le
  have hmono : Monotone (fun N => {ω | ∃ k ≤ N, c ≤ FreedmanAux.Zp F μ X l k ω}) :=
    fun N M hNM ω ⟨k, hk, hc⟩ => ⟨k, hk.trans hNM, hc⟩
  have hcμ : c * μ (⋃ N, {ω | ∃ k ≤ N, c ≤ FreedmanAux.Zp F μ X l k ω}) ≤ 1 := by
    rw [hmono.measure_iUnion, ENNReal.mul_iSup]
    exact iSup_le fun N => (FreedmanAux.maximal F (FreedmanAux.Zp F μ X l)
      (FreedmanAux.measurable_Zp F μ X l hX) hstep c N).trans hZ0.le
  have hc0 : 0 < Real.exp (l * a) * Real.exp (-(e * b)) := by positivity
  have hfin : μ (⋃ N, {ω | ∃ k ≤ N, c ≤ FreedmanAux.Zp F μ X l k ω}) ≤ c⁻¹ :=
    ENNReal.le_inv_iff_mul_le.2 (by rwa [mul_comm])
  have hcinv : c⁻¹ = ENNReal.ofReal ((Real.exp (l * a) * Real.exp (-(e * b)))⁻¹) := by
    rw [hc_def, ENNReal.ofReal_inv_of_pos hc0]
  rw [hcinv] at hfin
  refine (measure_mono hsub).trans (hfin.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  have hlog : Real.log (b / (a + b)) = -l := by
    rw [show b / (a + b) = (1 + a / b)⁻¹ by field_simp; ring, Real.log_inv, hl_def]
  rw [← Real.exp_add, ← Real.exp_neg, Real.rpow_def_of_pos (by positivity), ← Real.exp_add, hlog,
    he_def, hel]
  congr 1
  field_simp
  ring
