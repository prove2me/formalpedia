-- Prove2me | solution 1 for GaussianPerimeter.uniformSphere_cap_le_sectionRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:04.260414+00:00
-- url     : https://prove2.me/submissions/b81b5800-48af-444a-a73f-cba2f899e74b

module
public import Definitions.Def_GaussianPerimeter_Sphere
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Definitions.Def_GaussianPerimeter_SphereSections
public import Theorems.Thm_GaussianPerimeter_measurableSet_capCone
public import Theorems.Thm_GaussianPerimeter_uniformSphere_cap_eq_cone
public import Theorems.Thm_GaussianPerimeter_uniformSphere_cap_isometric

section
public section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace GaussianPerimeter
local notation "Euc" n => EuclideanSpace ℝ (Fin n)
private theorem volume_sections (n : ℕ) [NeZero n] {s : Set (ℝ × Euc n)}
    (hs : MeasurableSet s) {a b : ℝ} (hab : a ≤ b) (R : ℝ → ℝ) (hR : Continuous R)
    (hnonneg : ∀ x ∈ Ioc a b, 0 ≤ R x)
    (hsec : ∀ x, (volume : Measure (Euc n)) (Prod.mk x ⁻¹' s) =
      (Ioc a b).indicator (fun u => volume (Metric.ball (0 : Euc n) (R u))) x) :
    volume s = volume (Metric.ball (0 : Euc n) 1) *
      ENNReal.ofReal (∫ x in a..b, (R x) ^ n) := by
  change ((volume : Measure ℝ).prod (volume : Measure (Euc n))) s = _
  rw [Measure.prod_apply hs]
  simp_rw [hsec]
  rw [lintegral_indicator measurableSet_Ioc]
  have hpt (x : ℝ) (hx : x ∈ Ioc a b) :
      volume (Metric.ball (0 : Euc n) (R x)) =
        volume (Metric.ball (0 : Euc n) 1) * ENNReal.ofReal (R x ^ n) := by
    rw [Measure.addHaar_ball _ _ (hnonneg x hx), finrank_euclideanSpace_fin, mul_comm]
  have hRm : Measurable (fun x => ENNReal.ofReal (R x ^ n)) :=
    (hR.pow n).measurable.ennreal_ofReal
  have hRi : IntervalIntegrable (fun x : ℝ => R x ^ n) volume a b :=
    (hR.pow n).intervalIntegrable _ _
  rw [setLIntegral_congr_fun measurableSet_Ioc hpt, lintegral_const_mul _ hRm,
    intervalIntegral.integral_of_le hab,
    ofReal_integral_eq_lintegral_ofReal hRi.1]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact pow_nonneg (hnonneg x hx) _
local notation "W" n => WithLp 2 (ℝ × Euc n)
local notation "axis" n => (WithLp.toLp 2 ((1 : ℝ), (0 : Euc n)))
private theorem norm_sq_prod (n : ℕ) (z : ℝ × Euc n) :
    ‖WithLp.toLp 2 z‖ ^ 2 = z.1 ^ 2 + ‖z.2‖ ^ 2 := by
  simpa [Real.norm_eq_abs, sq_abs] using WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 z)
private theorem inner_axis (n : ℕ) (z : ℝ × Euc n) :
    ⟪axis n, WithLp.toLp 2 z⟫ = z.1 := by
  simp [WithLp.prod_inner_apply]
private theorem sliced_ball (n : ℕ) (z : ℝ × Euc n) :
    ‖WithLp.toLp 2 z‖ < 1 ↔
      z.1 ∈ Ioc (-1 : ℝ) 1 ∧ ‖z.2‖ < Real.sqrt (1 - z.1 ^ 2) := by
  rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one, one_pow, norm_sq_prod]
  constructor
  · intro h
    have hx : z.1 ∈ Ioc (-1 : ℝ) 1 := by
      refine ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg ‖z.2‖]
    refine ⟨hx, (Real.lt_sqrt (norm_nonneg _)).2 ?_⟩
    linarith
  · rintro ⟨hx, h⟩
    have he := (Real.lt_sqrt (norm_nonneg _)).1 h
    linarith
private theorem volume_ball_prod (n : ℕ) [NeZero n] :
    volume (Metric.ball (0 : W n) 1) =
      volume (Metric.ball (0 : Euc n) 1) *
      ENNReal.ofReal (∫ x in (-1 : ℝ)..1, (Real.sqrt (1 - x ^ 2)) ^ n) := by
  let R (x : ℝ) := Real.sqrt (1 - x ^ 2)
  let s : Set (ℝ × Euc n) := {z | z.1 ∈ Ioc (-1 : ℝ) 1 ∧ ‖z.2‖ < R z.1}
  have hR : Continuous R := by dsimp [R]; fun_prop
  have hs : MeasurableSet s :=
    (measurable_fst measurableSet_Ioc).inter (measurableSet_lt (by fun_prop) (hR.measurable.comp measurable_fst))
  have hpre : (@WithLp.toLp 2 (ℝ × Euc n)) ⁻¹' Metric.ball (0 : W n) 1 = s := by
    ext z
    simpa [Metric.mem_ball, dist_zero_right, s, R] using sliced_ball n z
  rw [← (WithLp.volume_preserving_toLp ℝ (Euc n)).measure_preimage measurableSet_ball.nullMeasurableSet, hpre]
  apply volume_sections n hs (by norm_num) R hR (fun _ _ => Real.sqrt_nonneg _)
  intro x
  by_cases hx : x ∈ Ioc (-1 : ℝ) 1
  · rw [indicator_of_mem hx]
    congr 1
    ext z
    simp only [mem_preimage, s, mem_ofPred_eq, hx, true_and, Metric.mem_ball, dist_zero_right]
  · simp only [indicator_of_notMem hx]
    have : Prod.mk x ⁻¹' s = ∅ := by ext; simp only [mem_preimage, s, mem_ofPred_eq, hx, false_and, mem_empty_iff_false]
    rw [this, measure_empty]
private theorem volume_capCone_prod_le (n : ℕ) [NeZero n] {t : ℝ} (ht : 0 < t)
    (ht₁ : t < 1) :
    volume (capCone (axis n) t) ≤ volume (Metric.ball (0 : Euc n) 1) *
      ENNReal.ofReal (t / ((n : ℝ) + 1) * (Real.sqrt (1 - t ^ 2)) ^ n +
        ∫ x in t..1, (Real.sqrt (1 - x ^ 2)) ^ n) := by
  let m := Real.sqrt (1 - t ^ 2) / t
  let r (x : ℝ) := x * m
  let R (x : ℝ) := Real.sqrt (1 - x ^ 2)
  let s₁ : Set (ℝ × Euc n) := {z | z.1 ∈ Ioc 0 t ∧ ‖z.2‖ ≤ r z.1}
  let s₂ : Set (ℝ × Euc n) := {z | z.1 ∈ Ioc t 1 ∧ ‖z.2‖ < R z.1}
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hR : Continuous R := by dsimp [R]; fun_prop
  have hs₁ : MeasurableSet s₁ :=
    (measurable_fst measurableSet_Ioc).inter (measurableSet_le (by fun_prop) (hr.measurable.comp measurable_fst))
  have hs₂ : MeasurableSet s₂ :=
    (measurable_fst measurableSet_Ioc).inter (measurableSet_lt (by fun_prop) (hR.measurable.comp measurable_fst))
  have hsub : (@WithLp.toLp 2 (ℝ × Euc n)) ⁻¹' capCone (axis n) t ⊆ s₁ ∪ s₂ := by
    intro z hz
    change 0 < ‖WithLp.toLp 2 z‖ ∧ ‖WithLp.toLp 2 z‖ < 1 ∧
      t * ‖WithLp.toLp 2 z‖ ≤ ⟪axis n, WithLp.toLp 2 z⟫ at hz
    rw [inner_axis] at hz
    have hx : 0 < z.1 := (mul_pos ht hz.1).trans_le hz.2.2
    have hball := (sliced_ball n z).1 hz.2.1
    by_cases hxt : z.1 ≤ t
    · left
      refine ⟨⟨hx, hxt⟩, ?_⟩
      have hsq := (sq_le_sq₀ (mul_nonneg ht.le (norm_nonneg _)) hx.le).2 hz.2.2
      rw [mul_pow, norm_sq_prod] at hsq
      have ht' : 0 ≤ 1 - t ^ 2 := by nlinarith
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hx.le hm)).1
      dsimp only [r, m]
      rw [mul_pow, div_pow, Real.sq_sqrt ht', ← mul_div_assoc]
      apply (le_div_iff₀ (sq_pos_of_pos ht)).2
      nlinarith [hsq]
    · exact Or.inr ⟨⟨lt_of_not_ge hxt, hball.1.2⟩, hball.2⟩
  have hvol₁ := volume_sections n hs₁ ht.le r hr (fun _ hx => mul_nonneg hx.1.le hm)
  have hv₁ : volume s₁ = _ := hvol₁ (by
    intro x
    by_cases hx : x ∈ Ioc 0 t
    · rw [indicator_of_mem hx, ← Measure.addHaar_closedBall_eq_addHaar_ball]
      congr 1
      ext y
      simp only [mem_preimage, s₁, mem_ofPred_eq, hx, true_and, Metric.mem_closedBall, dist_zero_right]
    · simp only [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' s₁ = ∅ := by ext; simp only [mem_preimage, s₁, mem_ofPred_eq, hx, false_and, mem_empty_iff_false]
      rw [this, measure_empty])
  have hvol₂ := volume_sections n hs₂ ht₁.le R hR (fun _ _ => Real.sqrt_nonneg _)
  have hv₂ : volume s₂ = _ := hvol₂ (by
    intro x
    by_cases hx : x ∈ Ioc t 1
    · rw [indicator_of_mem hx]
      congr 1
      ext y
      simp only [mem_preimage, s₂, mem_ofPred_eq, hx, true_and, Metric.mem_ball, dist_zero_right]
    · simp only [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' s₂ = ∅ := by ext; simp only [mem_preimage, s₂, mem_ofPred_eq, hx, false_and, mem_empty_iff_false]
      rw [this, measure_empty])
  have hint : (∫ x in 0..t, (r x)^n) =
      t / ((n : ℝ) + 1) * (Real.sqrt (1 - t ^ 2)) ^ n := by
    simp_rw [r, mul_pow, intervalIntegral.integral_mul_const, integral_pow, m, div_pow]
    have hn : 0 < n + 1 := Nat.succ_pos _
    rw [zero_pow hn.ne', sub_zero, pow_succ]
    have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.ne'
    have hpn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [htn, hpn]
  have hnn₁ : 0 ≤ t / ((n : ℝ) + 1) * (Real.sqrt (1 - t ^ 2)) ^ n := by positivity
  have hnn₂ : 0 ≤ ∫ x in t..1, (Real.sqrt (1 - x ^ 2)) ^ n :=
    intervalIntegral.integral_nonneg ht₁.le (fun _ _ => by positivity)
  rw [← (WithLp.volume_preserving_toLp ℝ (Euc n)).measure_preimage
    (measurableSet_capCone (axis n) t).nullMeasurableSet]
  calc
    _ ≤ volume (s₁ ∪ s₂) := measure_mono hsub
    _ ≤ volume s₁ + volume s₂ := measure_union_le _ _
    _ = _ := by
      rw [hv₁, hv₂, hint, ENNReal.ofReal_add hnn₁ hnn₂, mul_add]
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open GaussianPerimeter
local notation "Euc" n => EuclideanSpace ℝ (Fin n)
local notation "W" n => WithLp 2 (ℝ × Euc n)
local notation "axis" n => (WithLp.toLp 2 ((1 : ℝ), (0 : Euc n)))
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) [NeZero n] {v : Euc (n + 1)}
    (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    uniformSphere (Euc (n + 1)) {u | t ≤ ⟪v, (u : Euc (n + 1))⟫} ≤
      ENNReal.ofReal (t / ((n : ℝ) + 1) * (Real.sqrt (1 - t ^ 2)) ^ n +
        ∫ x in t..1, (Real.sqrt (1 - x ^ 2)) ^ n) /
      ENNReal.ofReal (∫ x in (-1 : ℝ)..1, (Real.sqrt (1 - x ^ 2)) ^ n) := by
  have hdim : Module.finrank ℝ (W n) = n + 1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × Euc n)).finrank_eq,
      Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
    exact Nat.add_comm _ _
  let e : (W n) ≃ₗᵢ[ℝ] (Euc (n + 1)) :=
    (stdOrthonormalBasis ℝ (W n)).repr.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim))
  have haxis : ‖axis n‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1
    rw [norm_sq_prod]; norm_num
  have heq : ‖e (axis n)‖ = ‖v‖ := by rw [e.norm_map, haxis, hv]
  let R : (Euc (n + 1)) ≃ₗᵢ[ℝ] (Euc (n + 1)) :=
    (ℝ ∙ (e (axis n) - v))ᗮ.reflection
  have hR : R (e (axis n)) = v := Submodule.reflection_sub heq
  rw [← hR]
  change uniformSphere (Euc (n + 1))
    {u | t ≤ ⟪(e.trans R) (axis n), (u : Euc (n + 1))⟫} ≤ _
  rw [← uniformSphere_cap_isometric (e.trans R), uniformSphere_cap_eq_cone,
    volume_ball_prod]
  have hU : volume (Metric.ball (0 : Euc n) 1) ≠ 0 :=
    Metric.isOpen_ball.measure_ne_zero _ (Metric.nonempty_ball.mpr zero_lt_one)
  have hUt : volume (Metric.ball (0 : Euc n) 1) ≠ ∞ := measure_ball_lt_top.ne
  refine (ENNReal.div_le_div_right (volume_capCone_prod_le n ht ht₁) _).trans_eq ?_
  exact ENNReal.mul_div_mul_left _ _ hU hUt
end GaussianPerimeter
