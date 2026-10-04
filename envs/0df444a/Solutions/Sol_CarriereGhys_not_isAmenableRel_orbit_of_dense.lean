-- Prove2me | solution 1 for CarriereGhys.not_isAmenableRel_orbit_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T07:09:27.847183+00:00
-- url     : https://prove2.me/submissions/ec705351-feb0-4a2f-82cc-90e2775b7804

import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_DenseSL2_exists_elliptic_infinite_order_of_dense
import Theorems.Thm_TitsLemma_exists_ringHom_proximal
import Theorems.Thm_PingPongSL2_exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal
import Mathlib


section
section
/-! Shared definitions for the Carrière–Ghys argument (Monod C9, `not_isAmenableRel_mob`). -/

namespace Monod.Dev.CG

open Matrix

variable {A : Subring ℝ}

/-- `a_t = [[t, -1], [1, 0]]`, elliptic when `|t| < 2`: `x ↦ t - 1/x`. -/
def ell (t : A) : SpecialLinearGroup (Fin 2) A :=
  ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

end Monod.Dev.CG

end
end

section
section
/-! A4 of the Carrière–Ghys argument: for `|t| < 2`, the elliptic Möbius map `a_t : x ↦ t - 1/x`
preserves the finite measure `dx / (x² - t x + 1)` on `P¹`, which has the same null sets as
`volP1`; so `a_t` is conservative and every a.e. wandering set for `a_t` is null. -/

namespace Monod.Dev.CG.A4

open MeasureTheory Matrix OnePoint Set Filter

variable {A : Subring ℝ}

/-! ### The Möbius action of `ell t` -/

lemma mob_mul (g h : SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (g * h) x = mob g (mob h x) := by
  unfold mob; rw [map_mul, mul_smul]

lemma mob_one (x : OnePoint ℝ) : mob (1 : SpecialLinearGroup (Fin 2) A) x = x := by
  unfold mob; rw [map_one, one_smul]

lemma mob_pow (g : SpecialLinearGroup (Fin 2) A) (n : ℕ) : mob (g ^ n) = (mob g)^[n] := by
  induction n with
  | zero => funext x; simp [mob_one]
  | succ n ih => funext x; rw [pow_succ, Function.iterate_succ_apply, mob_mul, ih]

lemma slToGL_apply (g : SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    (slToGL A g : GL (Fin 2) ℝ) i j = ((g i j : A) : ℝ) := by
  simp [slToGL]

lemma ell_apply (t : A) :
    ((ell t) 0 0 : ℝ) = t ∧ ((ell t) 0 1 : ℝ) = -1 ∧ ((ell t) 1 0 : ℝ) = 1 ∧
      ((ell t) 1 1 : ℝ) = 0 := by
  simp [ell]

lemma mob_ell_coe (t : A) (x : ℝ) (hx : x ≠ 0) :
    mob (ell t) (x : OnePoint ℝ) = (((t : ℝ) - x⁻¹ : ℝ) : OnePoint ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := ell_apply t
  unfold mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply, h1, h2, h3, h4]
  rw [if_neg (by simpa using hx)]
  congr 1
  rw [one_mul, add_zero, ← sub_eq_add_neg, sub_div, mul_div_assoc, div_self hx, mul_one, one_div]

lemma mob_ell_zero (t : A) : mob (ell t) ((0 : ℝ) : OnePoint ℝ) = ∞ := by
  obtain ⟨h1, h2, h3, h4⟩ := ell_apply t
  unfold mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply, h1, h2, h3, h4]
  simp

/-! ### The invariant weight `w(x) = 1 / (x² - τ x + 1)` -/

/-- The quadratic `x² - τ x + 1`. -/
noncomputable def qd (τ x : ℝ) : ℝ := x ^ 2 - τ * x + 1

/-- The density `w(x) = 1 / (x² - τ x + 1)`. -/
noncomputable def wt (τ x : ℝ) : ℝ := (qd τ x)⁻¹

/-- The map `x ↦ τ - 1/x` on `ℝ`. -/
noncomputable def fa (τ x : ℝ) : ℝ := τ - x⁻¹

lemma qd_pos {τ : ℝ} (hτ : |τ| < 2) (x : ℝ) : 0 < qd τ x := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hτ
  unfold qd
  nlinarith [mul_pos (sub_pos.2 h2) (by linarith : (0 : ℝ) < 2 + τ), sq_nonneg (2 * x - τ)]

lemma qd_ge {τ : ℝ} (hτ : |τ| < 2) (x : ℝ) : (1 - |τ| / 2) * (1 + x ^ 2) ≤ qd τ x := by
  unfold qd
  have h1 : τ * x ≤ |τ| * |x| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [sq_nonneg (1 - |x|), abs_nonneg τ, sq_abs x, abs_nonneg x]

lemma wt_pos {τ : ℝ} (hτ : |τ| < 2) (x : ℝ) : 0 < wt τ x := inv_pos.2 (qd_pos hτ x)

lemma continuous_wt {τ : ℝ} (hτ : |τ| < 2) : Continuous (wt τ) := by
  unfold wt qd
  exact Continuous.inv₀ (by fun_prop) (fun x => (qd_pos hτ x).ne')

lemma wt_le {τ : ℝ} (hτ : |τ| < 2) (x : ℝ) : wt τ x ≤ (1 - |τ| / 2)⁻¹ * (1 + x ^ 2)⁻¹ := by
  have hc : 0 < 1 - |τ| / 2 := by linarith
  unfold wt
  rw [← mul_inv]
  exact inv_anti₀ (mul_pos hc (by positivity)) (qd_ge hτ x)

lemma integrable_wt {τ : ℝ} (hτ : |τ| < 2) : Integrable (wt τ) := by
  refine (integrable_inv_one_add_sq.const_mul ((1 - |τ| / 2)⁻¹)).mono'
    (continuous_wt hτ).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (wt_pos hτ x)]
  exact wt_le hτ x

/-- The pointwise invariance identity `w(τ - 1/x) / x² = w(x)`. -/
lemma wt_fa {τ x : ℝ} (hx : x ≠ 0) : (x ^ 2)⁻¹ * wt τ (fa τ x) = wt τ x := by
  unfold wt fa qd
  rw [← mul_inv]
  congr 1
  field_simp
  ring

/-! ### Change of variables for `x ↦ τ - 1/x` -/

lemma image_fa_Ioi (τ : ℝ) : fa τ '' Ioi 0 = Iio τ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := inv_pos.2 (mem_Ioi.1 hx)
    simp only [mem_Iio, fa]
    linarith
  · intro hy
    refine ⟨(τ - y)⁻¹, inv_pos.2 (sub_pos.2 (mem_Iio.1 hy)), ?_⟩
    simp [fa]

lemma image_fa_Iio (τ : ℝ) : fa τ '' Iio 0 = Ioi τ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := inv_lt_zero.2 (mem_Iio.1 hx)
    simp only [mem_Ioi, fa]
    linarith
  · intro hy
    refine ⟨(τ - y)⁻¹, inv_lt_zero.2 (sub_neg.2 (mem_Ioi.1 hy)), ?_⟩
    simp [fa]

lemma injective_fa (τ : ℝ) : Function.Injective (fa τ) := fun x y h => by
  unfold fa at h
  exact inv_injective (by linarith)

lemma hasDerivAt_fa (τ : ℝ) {x : ℝ} (hx : x ≠ 0) : HasDerivAt (fa τ) ((x ^ 2)⁻¹) x := by
  have h := (hasDerivAt_inv hx).const_sub τ
  rw [neg_neg] at h
  exact h

lemma measurable_fa (τ : ℝ) : Measurable (fa τ) := measurable_const.sub measurable_inv

/-- Change of variables on a set avoiding `0`. -/
lemma lintegral_image_fa (τ : ℝ) {s : Set ℝ} (hs : MeasurableSet s) (hs0 : ∀ x ∈ s, x ≠ 0)
    (B : Set ℝ) :
    ∫⁻ y in fa τ '' s, B.indicator (fun y => ENNReal.ofReal (wt τ y)) y =
      ∫⁻ x in s, (fa τ ⁻¹' B).indicator (fun x => ENNReal.ofReal (wt τ x)) x := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun x hx => (hasDerivAt_fa τ (hs0 x hx)).hasDerivWithinAt) (injective_fa τ).injOn]
  refine setLIntegral_congr_fun hs (fun x hx => ?_)
  have hx0 := hs0 x hx
  have hpos : 0 < (x ^ 2)⁻¹ := inv_pos.2 (by positivity)
  rw [abs_of_pos hpos]
  by_cases hB : fa τ x ∈ B
  · rw [indicator_of_mem hB, indicator_of_mem (show x ∈ fa τ ⁻¹' B from hB),
      ← ENNReal.ofReal_mul hpos.le, wt_fa hx0]
  · rw [indicator_of_notMem hB, indicator_of_notMem (show x ∉ fa τ ⁻¹' B from hB), mul_zero]

/-- The measure `w(x) dx` on `ℝ`. -/
noncomputable def muR (τ : ℝ) : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (wt τ x))

lemma muR_apply (τ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    muR τ B = ∫⁻ x, B.indicator (fun x => ENNReal.ofReal (wt τ x)) x := by
  rw [muR, withDensity_apply _ hB, lintegral_indicator hB]

lemma lintegral_split (F : ℝ → ENNReal) (a : ℝ) :
    ∫⁻ x, F x = (∫⁻ x in Iio a, F x) + ∫⁻ x in Ioi a, F x := by
  rw [← lintegral_add_compl F (measurableSet_Iio (a := a)), compl_Iio,
    setLIntegral_congr Ioi_ae_eq_Ici.symm]

lemma muR_fa (τ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) : muR τ (fa τ ⁻¹' B) = muR τ B := by
  rw [muR_apply τ hB, muR_apply τ (measurable_fa τ hB),
    lintegral_split (B.indicator (fun x => ENNReal.ofReal (wt τ x))) τ,
    lintegral_split ((fa τ ⁻¹' B).indicator (fun x => ENNReal.ofReal (wt τ x))) 0,
    ← image_fa_Ioi τ, ← image_fa_Iio τ,
    lintegral_image_fa τ measurableSet_Ioi (fun x hx => (mem_Ioi.1 hx).ne') B,
    lintegral_image_fa τ measurableSet_Iio (fun x hx => (mem_Iio.1 hx).ne) B, add_comm]

lemma isFiniteMeasure_muR {τ : ℝ} (hτ : |τ| < 2) : IsFiniteMeasure (muR τ) :=
  isFiniteMeasure_withDensity_ofReal (integrable_wt hτ).hasFiniteIntegral

lemma muR_ae_ne (τ : ℝ) : ∀ᵐ x ∂(muR τ), x ≠ 0 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_iff.2 (by simp))

/-! ### Transport to `P¹` -/

lemma measurable_coeP : Measurable ((↑) : ℝ → OnePoint ℝ) := continuous_coe.measurable

lemma measurable_of_coe {f : OnePoint ℝ → OnePoint ℝ} (hf : Measurable (fun x : ℝ => f x)) :
    Measurable f := by
  intro S hS
  have : f ⁻¹' S = ((↑) : ℝ → OnePoint ℝ) '' ((fun x : ℝ => f x) ⁻¹' S) ∪ ({∞} ∩ f ⁻¹' S) := by
    ext p
    cases p with
    | infty => simp
    | coe x => simp
  rw [this]
  exact (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.2 (hf hS)).union
    ((Set.subsingleton_singleton.anti inter_subset_left).measurableSet)

lemma measurable_mob_ell (t : A) : Measurable (mob (ell t)) := by
  apply measurable_of_coe
  have : (fun x : ℝ => mob (ell t) x) =
      fun x : ℝ => if x = 0 then ∞ else ((fa t x : ℝ) : OnePoint ℝ) := by
    funext x
    split_ifs with h
    · rw [h]; exact mob_ell_zero t
    · exact mob_ell_coe t x h
  rw [this]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_coeP.comp (measurable_fa _))

/-- The measure `w(x) dx` transported to `P¹`. -/
noncomputable def nuP (τ : ℝ) : Measure (OnePoint ℝ) :=
  Measure.map ((↑) : ℝ → OnePoint ℝ) (muR τ)

lemma isFiniteMeasure_nuP {τ : ℝ} (hτ : |τ| < 2) : IsFiniteMeasure (nuP τ) := by
  have := isFiniteMeasure_muR hτ
  unfold nuP
  infer_instance

lemma nuP_ac (τ : ℝ) : nuP τ ≪ volP1 := by
  unfold nuP volP1 muR
  exact (withDensity_absolutelyContinuous _ _).map measurable_coeP

lemma volP1_ac {τ : ℝ} (hτ : |τ| < 2) : volP1 ≪ nuP τ := by
  unfold nuP volP1 muR
  exact (withDensity_absolutelyContinuous'
    (continuous_wt hτ).measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (wt_pos hτ x)).ne')).map measurable_coeP

lemma measurePreserving_mob_ell (t : A) :
    MeasurePreserving (mob (ell t)) (nuP t) (nuP t) := by
  refine ⟨measurable_mob_ell t, ?_⟩
  ext S hS
  rw [Measure.map_apply (measurable_mob_ell t) hS, nuP,
    Measure.map_apply measurable_coeP (measurable_mob_ell t hS),
    Measure.map_apply measurable_coeP hS, ← muR_fa (t : ℝ) (measurable_coeP hS)]
  apply measure_congr
  filter_upwards [muR_ae_ne (t : ℝ)] with x hx
  change (mob (ell t) (x : OnePoint ℝ) ∈ S) = (((fa t x : ℝ) : OnePoint ℝ) ∈ S)
  rw [mob_ell_coe t x hx]
  rfl

end Monod.Dev.CG.A4

namespace Monod.Dev.CG

open MeasureTheory Matrix

theorem chk_null_of_wandering {A : Subring ℝ} (t : A) (ht : |(t : ℝ)| < 2) (W : Set (OnePoint ℝ))
    (hW : NullMeasurableSet W volP1)
    (hwand : ∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (ell t ^ m) ⁻¹' W) = 0) : volP1 W = 0 := by
  have := A4.isFiniteMeasure_nuP ht
  have hcons := (A4.measurePreserving_mob_ell t).conservative
  have h1 := hcons.measure_mem_forall_ge_image_notMem_eq_zero (hW.mono_ac (A4.nuP_ac _)) 1
  have h2 : ∀ m : ℕ, A4.nuP (t : ℝ) (W ∩ (mob (ell t))^[m + 1] ⁻¹' W) = 0 := fun m => by
    apply A4.nuP_ac
    have := hwand ((m + 1 : ℕ) : ℤ) (by omega)
    rwa [zpow_natCast, A4.mob_pow] at this
  have hsub : W ⊆ {x ∈ W | ∀ m ≥ 1, (mob (ell t))^[m] x ∉ W} ∪
      ⋃ m : ℕ, (W ∩ (mob (ell t))^[m + 1] ⁻¹' W) := by
    intro x hx
    by_cases h : ∀ m ≥ 1, (mob (ell t))^[m] x ∉ W
    · exact Or.inl ⟨hx, h⟩
    · push Not at h
      obtain ⟨m, hm, hmW⟩ := h
      refine Or.inr (Set.mem_iUnion.2 ⟨m - 1, hx, ?_⟩)
      rwa [Set.mem_preimage, Nat.sub_add_cancel hm]
  exact A4.volP1_ac ht
    (measure_mono_null hsub (measure_union_null h1 (measure_iUnion_null h2)))

end Monod.Dev.CG

end
end

section
section
/-! # A8: the core of the Carrière–Ghys argument

A left invariant mean `P` on the orbit relation of `SL(2, A)` gives `u = P f_S`, where `f_S` is
the indicator of the pairs `(x, s x)` with `s ∈ S`.  Freeness off a countable set and the
ping-pong properties of `S` give `u + u ∘ b + u ∘ b² ≤ 1` and `1 ≤ u + u ∘ a^m` a.e.; the second
makes `{u < 1/2}` wandering for `a`, hence null, and the first is then contradictory. -/

namespace Monod.Dev.CG.A8

open Monod OnePoint Filter Topology Set MeasureTheory

variable {A : Subring ℝ}

/-! ### Möbius maps (copied from `DynBasic`) -/

/-- real entries -/
noncomputable abbrev ent (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) : ℝ :=
  ((g i j : A) : ℝ)

lemma slToGL_apply (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    (slToGL A g : GL (Fin 2) ℝ) i j = ent g i j := by
  simp [slToGL]

lemma det_ent (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun x : A => (x : ℝ)) h
  simpa using this

lemma mob_coe (g : Matrix.SpecialLinearGroup (Fin 2) A) (t : ℝ) :
    mob g (t : OnePoint ℝ) = if ent g 1 0 * t + ent g 1 1 = 0 then ∞ else
      (((ent g 0 0 * t + ent g 0 1) / (ent g 1 0 * t + ent g 1 1) : ℝ) : OnePoint ℝ) := by
  unfold mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply]

lemma mob_infty (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    mob g ∞ = if ent g 1 0 = 0 then ∞ else ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ) := by
  unfold mob
  rw [OnePoint.smul_infty_eq_ite]
  simp only [slToGL_apply]

lemma mob_mul (g h : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (g * h) x = mob g (mob h x) := by
  unfold mob
  rw [map_mul, mul_smul]

lemma mob_one (x : OnePoint ℝ) : mob (1 : Matrix.SpecialLinearGroup (Fin 2) A) x = x := by
  unfold mob
  rw [map_one, one_smul]

lemma mob_inv_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g⁻¹ (mob g x) = x := by
  rw [← mob_mul, inv_mul_cancel, mob_one]

lemma mob_mob_inv (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g (mob g⁻¹ x) = x := by
  rw [← mob_mul, mul_inv_cancel, mob_one]

lemma tendsto_coe_cobounded :
    Tendsto (fun x : ℝ => (x : OnePoint ℝ)) (Bornology.cobounded ℝ) (𝓝 ∞) := by
  rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact]
  exact tendsto_coe_infty

lemma tendsto_affine_cobounded {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    Tendsto (fun x : ℝ => c * x + d) (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 := tendsto_norm_cobounded_atTop (E := ℝ)
  have h2 : Tendsto (fun x : ℝ => |c| * ‖x‖ - |d|) (Bornology.cobounded ℝ) atTop := by
    apply tendsto_atTop_add_const_right
    exact h1.const_mul_atTop (abs_pos.2 hc)
  refine tendsto_atTop_mono (fun x => ?_) h2
  simp only [Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (c * x) (-d)
  rw [abs_mul, abs_neg, sub_neg_eq_add] at this
  linarith

lemma frac_eq (g : Matrix.SpecialLinearGroup (Fin 2) A) {x : ℝ} (hc : ent g 1 0 ≠ 0)
    (hx : ent g 1 0 * x + ent g 1 1 ≠ 0) :
    (ent g 0 0 * x + ent g 0 1) / (ent g 1 0 * x + ent g 1 1) =
      ent g 0 0 / ent g 1 0 - (ent g 1 0 * (ent g 1 0 * x + ent g 1 1))⁻¹ := by
  have := det_ent g
  rw [eq_sub_iff_add_eq, div_eq_mul_inv, mul_inv, ← add_mul, ← div_eq_mul_inv]
  rw [div_eq_div_iff hx hc, add_mul, inv_mul_cancel₀ hc]
  linear_combination (-1 : ℝ) * this

lemma continuous_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) : Continuous (mob g) := by
  have hdet := det_ent g
  rw [OnePoint.continuous_iff]
  constructor
  · rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    by_cases hc : ent g 1 0 = 0
    · have hd : ent g 1 1 ≠ 0 := by
        intro h; rw [h, hc] at hdet; simp at hdet
      rw [mob_infty, if_pos hc]
      have : (fun x : ℝ => mob g (x : OnePoint ℝ)) =
          fun x : ℝ => (((ent g 0 0 / ent g 1 1) * x + ent g 0 1 / ent g 1 1 : ℝ) : OnePoint ℝ) := by
        funext x
        rw [mob_coe, if_neg (by rw [hc]; simpa using hd)]
        congr 1
        rw [hc, zero_mul, zero_add]; field_simp
      rw [this]
      have ha : ent g 0 0 ≠ 0 := by
        intro h; rw [h, hc] at hdet; simp at hdet
      exact tendsto_coe_cobounded.comp (tendsto_affine_cobounded (div_ne_zero ha hd) _)
    · rw [mob_infty, if_neg hc]
      have hev : ∀ᶠ x : ℝ in Bornology.cobounded ℝ, ent g 1 0 * x + ent g 1 1 ≠ 0 := by
        have := (tendsto_affine_cobounded hc (ent g 1 1)).eventually
          (Bornology.eventually_ne_cobounded (0 : ℝ))
        exact this
      have hlim : Tendsto (fun x : ℝ => ((ent g 0 0 / ent g 1 0 -
          (ent g 1 0 * (ent g 1 0 * x + ent g 1 1))⁻¹ : ℝ) : OnePoint ℝ))
          (Bornology.cobounded ℝ) (𝓝 ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ)) := by
        apply (continuous_coe.tendsto _).comp
        have h3 : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1))
            (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
          have := tendsto_affine_cobounded (mul_ne_zero hc hc) (ent g 1 0 * ent g 1 1)
          refine this.congr (fun x => ?_)
          ring
        have h4 := (tendsto_inv₀_cobounded.comp h3)
        have := (tendsto_const_nhds (x := ent g 0 0 / ent g 1 0)).sub h4
        simpa using this
      refine hlim.congr' ?_
      filter_upwards [hev] with x hx
      rw [mob_coe, if_neg hx, frac_eq g hc hx]
  · rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : ent g 1 0 * t + ent g 1 1 = 0
    · have hc : ent g 1 0 ≠ 0 := by
        intro h; rw [h, zero_mul, zero_add] at ht; rw [ht, h] at hdet; simp at hdet
      show Tendsto (fun x : ℝ => mob g (x : OnePoint ℝ)) (𝓝 t) (𝓝 (mob g (t : OnePoint ℝ)))
      rw [mob_coe, if_pos ht, ← nhdsNE_sup_pure t, tendsto_sup]
      constructor
      · have h3 : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1))
            (𝓝[≠] t) (𝓝[≠] 0) := by
          apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          · have : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1)) (𝓝 t)
                (𝓝 (ent g 1 0 * (ent g 1 0 * t + ent g 1 1))) :=
              ((continuous_const.mul ((continuous_const.mul continuous_id).add
                continuous_const)).tendsto t)
            rw [ht, mul_zero] at this
            exact tendsto_nhdsWithin_of_tendsto_nhds this
          · filter_upwards [self_mem_nhdsWithin] with x hx
            simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
            intro h0
            rcases mul_eq_zero.1 h0 with h | h
            · exact hc h
            · apply hx
              have : ent g 1 0 * (x - t) = 0 := by linarith
              rcases mul_eq_zero.1 this with h' | h'
              · exact absurd h' hc
              · linarith
        have h4 := tendsto_inv₀_nhdsNE_zero.comp h3
        have h5 := (tendsto_const_add_cobounded (ent g 0 0 / ent g 1 0)).comp
          ((tendsto_neg_cobounded).comp h4)
        refine (tendsto_coe_cobounded.comp h5).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_compl_iff, mem_singleton_iff] at hx
        have hx' : ent g 1 0 * x + ent g 1 1 ≠ 0 := by
          intro h0; apply hx
          have : ent g 1 0 * (x - t) = 0 := by linarith
          rcases mul_eq_zero.1 this with h' | h'
          · exact absurd h' hc
          · linarith
        simp only [Function.comp_apply]
        rw [mob_coe, if_neg hx', frac_eq g hc hx', sub_eq_add_neg]
      · rw [tendsto_pure_left]
        intro s hs
        rw [mob_coe, if_pos ht]
        exact mem_of_mem_nhds hs
    · have hev : ∀ᶠ x : ℝ in 𝓝 t, ent g 1 0 * x + ent g 1 1 ≠ 0 :=
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt.eventually_ne ht
      have hcont : ContinuousAt (fun x : ℝ => (((ent g 0 0 * x + ent g 0 1) /
          (ent g 1 0 * x + ent g 1 1) : ℝ) : OnePoint ℝ)) t := by
        apply continuous_coe.continuousAt.comp
        exact (((continuous_const.mul continuous_id).add continuous_const).continuousAt).div
          (((continuous_const.mul continuous_id).add continuous_const).continuousAt) ht
      refine hcont.congr (Filter.EventuallyEq.symm ?_)
      filter_upwards [hev] with x hx
      rw [mob_coe, if_neg hx]

lemma measurable_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) : Measurable (mob g) :=
  (continuous_mob g).measurable

/-! ### Measurability on `P¹ × P¹` -/

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

attribute [local instance] secondCountable_P1

theorem countable_SL (A : Subring ℝ) [Countable A] :
    Countable (Matrix.SpecialLinearGroup (Fin 2) A) :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → A // Matrix.det M = 1})

attribute [local instance] countable_SL

section Bdd

variable {X : Type*} [MeasurableSpace X]

lemma isBddMeasOn_add {R : Set (X × X)} {f g : X × X → ℝ} (hf : IsBddMeasOn R f)
    (hg : IsBddMeasOn R g) : IsBddMeasOn R (f + g) := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  exact ⟨hf.1.add hg.1, C + D, fun p hp => (abs_add_le _ _).trans (add_le_add (hC p hp) (hD p hp))⟩

lemma isBddMeasOn_smul {R : Set (X × X)} (c : ℝ) {f : X × X → ℝ} (hf : IsBddMeasOn R f) :
    IsBddMeasOn R (c • f) := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨hf.1.const_smul c, |c| * C, fun p hp => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg c)

lemma isBddMeasOn_one (R : Set (X × X)) : IsBddMeasOn R (1 : X × X → ℝ) :=
  ⟨measurable_const, 1, fun p _ => by simp⟩

/-- Monotonicity of a left invariant mean, for an inequality holding off a null set of first
coordinates. -/
lemma ae_le_of_le {μ : Measure X} {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ}
    (hP : IsLeftInvariantMean μ R P) {f g : X × X → ℝ} (hf : IsBddMeasOn R f)
    (hg : IsBddMeasOn R g) {N : Set X} (hN : μ N = 0) (hle : ∀ p ∈ R, p.1 ∉ N → f p ≤ g p) :
    ∀ᵐ x ∂μ, P f x ≤ P g x := by
  set h : X × X → ℝ := g + (-1 : ℝ) • f with hh_def
  have hh : IsBddMeasOn R h := isBddMeasOn_add hg (isBddMeasOn_smul _ hf)
  set h' : X × X → ℝ := fun p => max (h p) 0 with hh'_def
  have hh' : IsBddMeasOn R h' := by
    obtain ⟨C, hC⟩ := hh.2
    refine ⟨hh.1.max measurable_const, C, fun p hp => ?_⟩
    refine le_trans ?_ (hC p hp)
    rw [abs_le]
    constructor
    · linarith [le_max_right (h p) 0, abs_nonneg (h p)]
    · exact max_le (le_abs_self _) (abs_nonneg _)
  have h0 : ∀ᵐ x ∂μ, 0 ≤ P h' x := hP.nonneg h' hh' fun p _ => le_max_right _ _
  have hc : P h' =ᵐ[μ] P h := by
    refine hP.congr h' h hh' hh (measure_mono_null ?_ hN)
    rintro _ ⟨p, ⟨hne, hR⟩, rfl⟩
    by_contra hpN
    apply hne
    have := hle p hR hpN
    show max (h p) 0 = h p
    apply max_eq_left
    simp only [hh_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hadd : P h =ᵐ[μ] P g + P ((-1 : ℝ) • f) := hP.add g _ hg (isBddMeasOn_smul _ hf)
  have hsm : P ((-1 : ℝ) • f) =ᵐ[μ] (-1 : ℝ) • P f := hP.smul _ f hf
  filter_upwards [h0, hc, hadd, hsm] with x h0 hc hadd hsm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsm
  rw [hc, hadd, hsm] at h0
  linarith

end Bdd

/-! ### The global partial transformations `φ_g` -/

/-- `x ↦ mob g⁻¹ x` as a measurable equivalence, with inverse `mob g`. -/
noncomputable def mobInvME (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    OnePoint ℝ ≃ᵐ OnePoint ℝ where
  toFun := mob g⁻¹
  invFun := mob g
  left_inv := mob_mob_inv g
  right_inv := mob_inv_mob g
  measurable_toFun := measurable_mob g⁻¹
  measurable_invFun := measurable_mob g

/-! ### Null sets of `volP1` -/

lemma volP1_apply (Z : Set (OnePoint ℝ)) : volP1 Z = volume (((↑) : ℝ → OnePoint ℝ) ⁻¹' Z) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.map_apply volume Z

lemma volP1_univ : volP1 (univ : Set (OnePoint ℝ)) = ⊤ := by
  rw [volP1_apply, preimage_univ, Real.volume_univ]

lemma volP1_of_countable {Z : Set (OnePoint ℝ)} (hZ : Z.Countable) : volP1 Z = 0 := by
  rw [volP1_apply]
  exact (hZ.preimage OnePoint.coe_injective).measure_zero _

/-- Möbius maps send null sets to null sets (copied from `RedNull`). -/
lemma null_image_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) {S : Set (OnePoint ℝ)}
    (hS : volP1 S = 0) : volP1 (mob g '' S) = 0 := by
  rw [volP1_apply] at hS ⊢
  set a : ℝ := ((g 0 0 : A) : ℝ)
  set b : ℝ := ((g 0 1 : A) : ℝ)
  set c : ℝ := ((g 1 0 : A) : ℝ)
  set d : ℝ := ((g 1 1 : A) : ℝ)
  let φ : ℝ → ℝ := fun x => (a * x + b) / (c * x + d)
  let U : Set ℝ := {x | c * x + d ≠ 0}
  have hφ : DifferentiableOn ℝ φ (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact hx.2
  have h1 : volume (φ '' (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hφ
      (measure_mono_null Set.inter_subset_left hS)
  have hsub : ((↑) : ℝ → OnePoint ℝ) ⁻¹' (mob g '' S) ⊆
      φ '' (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U) ∪ ((↑) : ℝ → OnePoint ℝ) ⁻¹' {mob g ∞} := by
    rintro y ⟨z, hz, hzy⟩
    cases z with
    | infty => exact Or.inr (by simp [← hzy])
    | coe x =>
      left
      rw [mob, OnePoint.smul_some_eq_ite] at hzy
      split_ifs at hzy with hx
      · exact absurd hzy.symm (OnePoint.coe_ne_infty y)
      · exact ⟨x, ⟨hz, hx⟩, OnePoint.coe_injective hzy⟩
  refine measure_mono_null hsub (measure_union_null h1 ?_)
  exact (Set.countable_singleton _).preimage OnePoint.coe_injective |>.measure_zero _

lemma null_preimage_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) {S : Set (OnePoint ℝ)}
    (hS : volP1 S = 0) : volP1 (mob g ⁻¹' S) = 0 := by
  have : mob g ⁻¹' S = mob g⁻¹ '' S := by
    ext x
    constructor
    · intro hx; exact ⟨mob g x, hx, mob_inv_mob g x⟩
    · rintro ⟨y, hy, rfl⟩; simpa [Set.mem_preimage, mob_mob_inv] using hy
  rw [this]
  exact null_image_mob g⁻¹ hS

/-! ### Freeness off a countable set -/

lemma not_scalar {g : Matrix.SpecialLinearGroup (Fin 2) A} (hg1 : g ≠ 1) (hg2 : g ≠ -1) :
    (slToGL A g).val ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨a, ha⟩
  have e : ∀ i j, ((g i j : A) : ℝ) = Matrix.scalar (Fin 2) a i j := fun i j => by
    rw [ha]; rfl
  have h00 := e 0 0
  have h11 := e 1 1
  have h01 := e 0 1
  have h10 := e 1 0
  simp at h00 h11 h01 h10
  have hdet := det_ent g
  simp only [ent] at hdet
  rw [h00, h11, h01, h10] at hdet
  have ha2 : (a - 1) * (a + 1) = 0 := by push_cast at hdet; linarith
  rcases mul_eq_zero.1 ha2 with h | h
  · apply hg1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply Subtype.ext
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10] <;> linarith
  · apply hg2
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply Subtype.ext
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg, h00, h11, h01, h10] <;>
      linarith

lemma countable_fix {g : Matrix.SpecialLinearGroup (Fin 2) A} (hg1 : g ≠ 1) (hg2 : g ≠ -1) :
    {x | mob g x = x}.Countable := by
  have hne : (slToGL A g).fixpointPolynomial ≠ 0 := by
    rw [Ne, Matrix.GeneralLinearGroup.fixpointPolynomial_eq_zero_iff]
    exact not_scalar hg1 hg2
  have hfin : {x : ℝ | ((slToGL A g).fixpointPolynomial).IsRoot x}.Finite :=
    Polynomial.finite_setOfPred_isRoot hne
  refine Set.Finite.countable (((hfin.image ((↑) : ℝ → OnePoint ℝ)).insert ∞).subset ?_)
  intro p hp
  cases p with
  | infty => exact Set.mem_insert _ _
  | coe x =>
    refine Set.mem_insert_of_mem _ ⟨x, ?_, rfl⟩
    have := (Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff
      (c := x) (g := slToGL A g)).2 hp
    simpa [Polynomial.aeval_def] using this

/-! ### The two pointwise inequalities -/

end Monod.Dev.CG.A8

namespace Monod.Dev.CG

open MeasureTheory Matrix

end Monod.Dev.CG

end
end

section
section
open MeasureTheory Matrix Filter Topology

namespace CyclotomicTrace

open Polynomial

end CyclotomicTrace

end
end

section
section
/-!
# A dense subgroup of `SL(2, ℝ)` contains an elliptic element of infinite order

Route (ported from Lodha–Moore statement 7, part G1):
* Jørgensen's sequence `B₀ = B`, `B_{n+1} = B_n A B_n⁻¹` gives, inside a two-generator subgroup
  of `Γ`, nontrivial elements `x n ≠ ±1` tending to `1`;
* a finitely generated subring of `ℝ` contains only finitely many numbers `z + z⁻¹` with `z` a
  root of unity (`CyclotomicTrace.finite_add_inv_rootOfUnity`);
* density gives four elliptic elements of `Γ` whose matrices span `M₂(ℝ)`; if every elliptic
  element of the finitely generated group were of finite order, the traces `tr (y i * x n)` would
  be eventually constant, so the trace pairing against `x n - 1` would vanish on a basis, forcing
  `x n = 1`.
-/

open Matrix Filter Topology

namespace DenseSL2

/-- `SL(2, ℝ)`. -/
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The entries of an element of `SL(2, ℝ)`. -/
abbrev ent (g : SL2) (i j : Fin 2) : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) i j

/-! ### Entries -/

/-- An element of `SL(2, ℝ)` from its entries. -/
def mk2 (p q r s : ℝ) (h : p * s - q * r = 1) : SL2 :=
  ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact h⟩

@[simp] lemma ent_mk2_00 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 0 = p := rfl
@[simp] lemma ent_mk2_01 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 1 = q := rfl
@[simp] lemma ent_mk2_10 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 0 = r := rfl
@[simp] lemma ent_mk2_11 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 1 = s := rfl

@[simp] lemma ent_inv_00 (g : SL2) : ent g⁻¹ 0 0 = ent g 1 1 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_01 (g : SL2) : ent g⁻¹ 0 1 = - ent g 0 1 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_10 (g : SL2) : ent g⁻¹ 1 0 = - ent g 1 0 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_11 (g : SL2) : ent g⁻¹ 1 1 = ent g 0 0 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-! ### Jørgensen's identity -/

/-! ### The entrywise `ℓ¹` norm -/

/-! ### Jørgensen's sequence -/

/-! ### The explicit pair and the choice by density -/

/-! ### The trace-pairing argument -/

/-! ### Four linearly independent elliptic elements -/

/-! ### Assembly -/

end DenseSL2

end
end

section
section
open MeasureTheory Matrix Filter Topology

namespace TitsLemma

open Cardinal Polynomial

end TitsLemma

end
end

section
section
/-!
# Part 3P: ping-pong over a normed field

`x ∈ SL(2, L)` with eigenvalues `μ, μ⁻¹`, `‖μ‖ > 1`, and `y = c x c⁻¹` sharing no eigenvector with
`x` (`tr [x, y] ≠ 2`). We conjugate `x` to `D = diag(μ, μ⁻¹)`; then `y` becomes `g⁻¹ D g` with all
four entries of `g` nonzero. On nonzero vectors of `L²` the sets `Bp ε = {‖u₁‖ ≤ ε ‖u₀‖}` and
`Bm ε = {‖u₀‖ ≤ ε ‖u₁‖}` (and their pull-backs by `g`) are ping-pong sets for `Dᴺ`, `g⁻¹ Dᴺ g`,
and Mathlib's `FreeGroup.injective_lift_of_ping_pong` gives freeness. `-1 ∉ range` follows from
injectivity, since free groups are torsion-free and `(-1)² = 1 ≠ -1`.
-/

open MeasureTheory Matrix Filter Topology

namespace PingPongSL2

open scoped Pointwise

section Vectors

variable {L : Type} [NormedField L]

end Vectors

section Diag

variable {L : Type} [NormedField L]

end Diag

section PingPong

variable {L : Type} [NormedField L]

end PingPong

section Diagonalize

variable {L : Type} [NormedField L]

end Diagonalize

end PingPongSL2

end
end

section
section
/-!
# Carrière–Ghys for an arbitrary countable dense subgroup of `PSL(2, ℝ)`

The orbit relation on `P¹` of a countable dense subgroup `Γ ≤ PSL(2, ℝ)` is not amenable in the
sense of Connes–Feldman–Weiss. The preimage `Γ̃ ≤ SL(2, ℝ)` of `Γ` contains

* an elliptic element `a₀` of infinite order (`DenseSL2.exists_elliptic_infinite_order_of_dense`,
  transported from `SL(2, ℝ)` to `SL(2, ⊤)` along the entrywise isomorphism);
* a conjugate `c` of `a₀` such that, after a Tits embedding of the entry field into a normed field
  (`TitsLemma.exists_ringHom_proximal`), ping-pong (`PingPongSL2.exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal`)
  makes `a = a₀ ^ N`, `b = c a₀ ^ N c⁻¹` a free pair avoiding `-1`.

Every elliptic element is conservative (it is conjugate to Monod's `a_t`), so every a.e. wandering
set of `a` is null; the free pair gives a ping-pong set `S ⊆ Γ̃` (reduced words ending in a power of
`a`), and the Carrière–Ghys argument (`not_isAmenableRel_relL`) turns a left invariant mean into a
contradiction.
-/

namespace CarriereGhys

open Monod Monod.Dev.CG.A8 Filter Topology Set MeasureTheory Matrix

/-! ## Basics on `SL(2, ℝ)` over `⊤ : Subring ℝ` -/

abbrev SLR := SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)
abbrev PSLR := ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)

/-- The quotient map `SL(2, ℝ) → PSL(2, ℝ)`. -/
noncomputable abbrev pr : SLR →* PSLR := QuotientGroup.mk' _

lemma slr_ext {A B : SLR} (h : ∀ i j, ent A i j = ent B i j) : A = B := by
  ext i j
  exact h i j

lemma ent_mul (A B : SLR) (i j : Fin 2) :
    ent (A * B) i j = ent A i 0 * ent B 0 j + ent A i 1 * ent B 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

lemma ent_one (i j : Fin 2) : ent (1 : SLR) i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [ent]

/-- A matrix of `SL(2, ℝ)` (over `⊤ : Subring ℝ`) from its real entries. -/
noncomputable def mk2 (p q r s : ℝ) (h : p * s - q * r = 1) : SLR :=
  ⟨!![⟨p, trivial⟩, ⟨q, trivial⟩; ⟨r, trivial⟩, ⟨s, trivial⟩], by
    rw [Matrix.det_fin_two_of]
    ext
    simpa using h⟩

@[simp] lemma ent_mk2_00 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 0 = p := rfl
@[simp] lemma ent_mk2_01 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 1 = q := rfl
@[simp] lemma ent_mk2_10 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 0 = r := rfl
@[simp] lemma ent_mk2_11 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 1 = s := rfl

@[simp] lemma ent_inv_00 (g : SLR) : ent g⁻¹ 0 0 = ent g 1 1 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_01 (g : SLR) : ent g⁻¹ 0 1 = - ent g 0 1 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_10 (g : SLR) : ent g⁻¹ 1 0 = - ent g 1 0 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_11 (g : SLR) : ent g⁻¹ 1 1 = ent g 0 0 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

lemma ent_neg_one (i j : Fin 2) : ent (-1 : SLR) i j = -(if i = j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> simp [ent, Matrix.SpecialLinearGroup.coe_neg]

lemma neg_one_mem_center : (-1 : SLR) ∈ Subgroup.center SLR :=
  Subgroup.mem_center_iff.2 fun g => by rw [neg_one_mul, mul_neg_one]

lemma neg_one_mem_comap (Γ : Subgroup PSLR) : (-1 : SLR) ∈ Γ.comap pr := by
  show pr (-1 : SLR) ∈ Γ
  rw [show pr (-1 : SLR) = 1 from (QuotientGroup.eq_one_iff (-1 : SLR)).2 neg_one_mem_center]
  exact Γ.one_mem

lemma ent_of_mem_center {z : SLR} (hz : z ∈ Subgroup.center SLR) :
    ∃ r : ℝ, r ^ 2 = 1 ∧ ent z 0 0 = r ∧ ent z 1 1 = r ∧ ent z 0 1 = 0 ∧ ent z 1 0 = 0 := by
  obtain ⟨r, hr1, hr2⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have e : ∀ i j, (z : Matrix (Fin 2) (Fin 2) (⊤ : Subring ℝ)) i j =
      (Matrix.scalar (Fin 2) r) i j := fun i j => by rw [hr2]
  refine ⟨(r : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hr1
    simpa using this
  · simp [ent, e 0 0]
  · simp [ent, e 1 1]
  · simp [ent, e 0 1]
  · simp [ent, e 1 0]

lemma eq_or_eq_neg_of_pr_eq {γ δ : SLR}
    (h : (QuotientGroup.mk γ : PSLR) = QuotientGroup.mk δ) : δ = γ ∨ δ = -γ := by
  have hz := QuotientGroup.eq.1 h
  obtain ⟨r, hr, h00, h11, h01, h10⟩ := ent_of_mem_center hz
  generalize hz' : γ⁻¹ * δ = z at h00 h11 h01 h10
  have e : δ = γ * z := by rw [← hz']; group
  have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rw [e]
  have ent_neg : ∀ (A : SLR) (i j : Fin 2), ent (-A) i j = -ent A i j := fun A i j => by
    simp [ent, Matrix.SpecialLinearGroup.coe_neg]
  rcases mul_eq_zero.1 hr' with h | h
  · left
    have hr1 : r = 1 := by linarith
    have hz1 : z = 1 := by
      apply slr_ext; intro i j
      rw [ent_one]
      fin_cases i <;> fin_cases j
      · simpa [hr1] using h00
      · simpa using h01
      · simpa using h10
      · simpa [hr1] using h11
    rw [hz1, mul_one]
  · right
    have hr1 : r = -1 := by linarith
    have hz1 : z = -1 := by
      apply slr_ext; intro i j
      rw [ent_neg, ent_one]
      fin_cases i <;> fin_cases j
      · simpa [hr1] using h00
      · simpa using h01
      · simpa using h10
      · simpa [hr1] using h11
    rw [hz1, mul_neg_one]

lemma countable_comap (Γ : Subgroup PSLR) [Countable Γ] : Countable (Γ.comap pr) := by
  classical
  let f : Γ.comap pr → Γ × Bool := fun γ =>
    (⟨QuotientGroup.mk (γ : SLR), γ.2⟩,
      decide ((γ : SLR) = Quotient.out (QuotientGroup.mk (γ : SLR) : PSLR)))
  refine Function.Injective.countable (f := f) fun γ δ hfg => ?_
  simp only [f, Prod.mk.injEq] at hfg
  obtain ⟨h1, h2⟩ := hfg
  have h1' : (QuotientGroup.mk (γ : SLR) : PSLR) = QuotientGroup.mk (δ : SLR) :=
    congrArg Subtype.val h1
  apply Subtype.ext
  have ho : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (γ : SLR) : PSLR)) : PSLR) =
      QuotientGroup.mk (γ : SLR) := QuotientGroup.out_eq' _
  have hγ := eq_or_eq_neg_of_pr_eq ho
  have hδ := eq_or_eq_neg_of_pr_eq (ho.trans h1')
  have hout : Quotient.out (QuotientGroup.mk (δ : SLR) : PSLR) =
      Quotient.out (QuotientGroup.mk (γ : SLR) : PSLR) := by rw [h1']
  rw [hout] at h2
  revert h2 hγ hδ
  generalize Quotient.out (QuotientGroup.mk (γ : SLR) : PSLR) = o
  intro h2 hγ hδ
  by_cases hg : (γ : SLR) = o
  · have hd : (δ : SLR) = o := by simpa [hg] using h2
    rw [hg, hd]
  · have hd : (δ : SLR) ≠ o := by simpa [hg] using h2
    have hg' : (γ : SLR) = -o := hγ.resolve_left (Ne.symm hg ∘ Eq.symm)
    have hd' : (δ : SLR) = -o := hδ.resolve_left (Ne.symm hd ∘ Eq.symm)
    rw [hg', hd']

/-- Density, pulled back to `SL(2, ℝ)`. -/
theorem exists_mem_of_isOpen (Γ : Subgroup PSLR) (hΓ : Dense (Γ : Set PSLR)) {U : Set SLR}
    (hU : IsOpen U) (hne : U.Nonempty) : ∃ g ∈ Γ.comap pr, g ∈ U := by
  obtain ⟨g, hg⟩ := hne
  obtain ⟨γ, ⟨u, hu, rfl⟩, hγ⟩ :=
    hΓ.inter_open_nonempty (pr '' U) (QuotientGroup.isOpenMap_coe U hU) ⟨pr g, g, hg, rfl⟩
  exact ⟨u, hγ, hu⟩

/-! ## The Carrière–Ghys argument for a countable subgroup `Λ` of `SL(2, ℝ)`

Monod's development (`Monod.Dev.CG.A8`) runs the argument for the orbit relation of `SL(2, A)`;
here it is run for the orbit relation of any countable subgroup `Λ` containing a conservative `a`,
an element `b` and a ping-pong set `S ⊆ Λ`. -/

section CGL

attribute [local instance] Monod.Dev.CG.A8.secondCountable_P1

variable (Λ : Subgroup SLR)

/-- The orbit relation of `Λ` on `P¹`. -/
def relL : Set (OnePoint ℝ × OnePoint ℝ) := {p | ∃ g ∈ Λ, mob g p.1 = p.2}

/-- The pairs `(x, s x)` with `s ∈ T`. -/
def grS (T : Set SLR) : Set (OnePoint ℝ × OnePoint ℝ) := {p | ∃ s ∈ T, mob s p.1 = p.2}

/-- `f_T`, the indicator of `grS T`. -/
noncomputable def indS (T : Set SLR) : OnePoint ℝ × OnePoint ℝ → ℝ := (grS T).indicator 1

open Classical in
lemma indS_apply (T : Set SLR) (p : OnePoint ℝ × OnePoint ℝ) :
    indS T p = if p ∈ grS T then 1 else 0 := by
  simp only [indS, Set.indicator_apply, Pi.one_apply]

lemma measurableSet_grS {T : Set SLR} (hT : T.Countable) : MeasurableSet (grS T) := by
  have : grS T = ⋃ s ∈ T, {p : OnePoint ℝ × OnePoint ℝ | mob s p.1 = p.2} := by
    ext p; simp [grS]
  rw [this]
  exact MeasurableSet.biUnion hT fun s _ =>
    measurableSet_eq_fun ((measurable_mob s).comp measurable_fst) measurable_snd

lemma isBddMeasOn_indS (R : Set (OnePoint ℝ × OnePoint ℝ)) {T : Set SLR} (hT : T.Countable) :
    IsBddMeasOn R (indS T) := by
  refine ⟨measurable_one.indicator (measurableSet_grS hT), 1, fun p _ => ?_⟩
  rw [indS_apply]
  split_ifs <;> norm_num

variable {Λ}

/-- The partial transformation `x ↦ mob g⁻¹ x` of `relL Λ`, for `g ∈ Λ`. -/
noncomputable def phiL {g : SLR} (hg : g ∈ Λ) : PartialTransformation (relL Λ) where
  dom := univ
  cod := univ
  measurableSet_dom := MeasurableSet.univ
  measurableSet_cod := MeasurableSet.univ
  e := ((MeasurableEquiv.Set.univ _).trans (mobInvME g)).trans (MeasurableEquiv.Set.univ _).symm
  graph_subset _ := ⟨g⁻¹, Λ.inv_mem hg, rfl⟩

lemma shiftRel_phiL {g : SLR} (hg : g ∈ Λ) (f : OnePoint ℝ × OnePoint ℝ → ℝ) :
    (phiL hg).shiftRel f = fun p => f (mob g p.1, p.2) := by
  funext p
  have h : p.1 ∈ (phiL hg).cod := mem_univ _
  simp only [PartialTransformation.shiftRel, dif_pos h]
  rfl

lemma shiftBase_phiL {g : SLR} (hg : g ∈ Λ) (F : OnePoint ℝ → ℝ) :
    (phiL hg).shiftBase F = F ∘ mob g := by
  funext y
  have h : y ∈ (phiL hg).cod := mem_univ _
  simp only [PartialTransformation.shiftBase, dif_pos h, Function.comp_apply]
  rfl

lemma mem_grS_shift (g : SLR) (T : Set SLR) (x y : OnePoint ℝ) :
    (mob g x, y) ∈ grS T ↔ (x, y) ∈ grS {s | s * g⁻¹ ∈ T} := by
  constructor
  · rintro ⟨s, hs, hsy⟩
    refine ⟨s * g, by simpa using hs, ?_⟩
    simp only at hsy ⊢
    rw [mob_mul, hsy]
  · rintro ⟨s, hs, hsy⟩
    refine ⟨s * g⁻¹, hs, ?_⟩
    simp only at hsy ⊢
    rw [mob_mul, mob_inv_mob, hsy]

lemma shiftRel_indS {g : SLR} (hg : g ∈ Λ) (T : Set SLR) :
    (phiL hg).shiftRel (indS T) = indS {s | s * g⁻¹ ∈ T} := by
  rw [shiftRel_phiL]
  funext ⟨x, y⟩
  classical
  simp only [indS, Set.indicator_apply, mem_grS_shift, Pi.one_apply]

lemma P_indS_shift {P : (OnePoint ℝ × OnePoint ℝ → ℝ) → OnePoint ℝ → ℝ}
    (hP : IsLeftInvariantMean volP1 (relL Λ) P) {g : SLR} (hg : g ∈ Λ) {T : Set SLR}
    (hT : T.Countable) :
    P (indS {s | s * g⁻¹ ∈ T}) =ᵐ[volP1] P (indS T) ∘ mob g := by
  have := hP.invariant (phiL hg) (indS T) (isBddMeasOn_indS _ hT)
  rwa [shiftRel_indS, shiftBase_phiL] at this

/-- The points with a nontrivial stabilizer in `Λ / ±1`. -/
def N0L (Λ : Subgroup SLR) : Set (OnePoint ℝ) :=
  {x | ∃ g ∈ Λ, g ≠ 1 ∧ g ≠ -1 ∧ mob g x = x}

lemma volP1_N0L [Countable Λ] : volP1 (N0L Λ) = 0 := by
  apply Monod.Dev.CG.A8.volP1_of_countable
  have : N0L Λ ⊆ ⋃ g : Λ, {x | (g : SLR) ≠ 1 ∧ (g : SLR) ≠ -1 ∧ mob (g : SLR) x = x} := by
    rintro x ⟨g, hg, h⟩
    exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, h⟩
  refine Set.Countable.mono this (Set.countable_iUnion fun g => ?_)
  by_cases h : (g : SLR) ≠ 1 ∧ (g : SLR) ≠ -1
  · exact (Monod.Dev.CG.A8.countable_fix h.1 h.2).mono fun x hx => hx.2.2
  · exact Set.Subsingleton.countable fun x hx => absurd ⟨hx.1, hx.2.1⟩ h

lemma eq_or_eq_negL {x : OnePoint ℝ} (hx : x ∉ N0L Λ) {g h : SLR} (hg : g ∈ Λ) (hh : h ∈ Λ)
    (hgh : mob g x = mob h x) : g = h ∨ g = -h := by
  by_contra hne
  rw [not_or] at hne
  apply hx
  refine ⟨h⁻¹ * g, Λ.mul_mem (Λ.inv_mem hh) hg, fun e => hne.1 ?_, fun e => hne.2 ?_, ?_⟩
  · exact (inv_mul_eq_one.1 e).symm
  · calc g = h * (h⁻¹ * g) := by group
      _ = -h := by rw [e, mul_neg, mul_one]
  · rw [mob_mul, hgh, mob_inv_mob]

lemma mul_mem_of_freeL {S : Set SLR} (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S) {x : OnePoint ℝ}
    (hx : x ∉ N0L Λ) {g h : SLR} (hg : g ∈ Λ) (hh : h ∈ Λ) (hgh : mob g x = mob h x)
    (c : SLR) (hhc : h * c ∈ S) : g * c ∈ S := by
  rcases eq_or_eq_negL hx hg hh hgh with rfl | rfl
  · exact hhc
  · rwa [neg_mul, hS]

lemma indS_three_le {S : Set SLR} (hSL : S ⊆ Λ) (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S) {b : SLR}
    (hbL : b ∈ Λ) (hb : ∀ δ ∈ S, δ * b ∉ S ∧ δ * b ^ 2 ∉ S)
    (p : OnePoint ℝ × OnePoint ℝ) (hp : p.1 ∉ N0L Λ) :
    indS S p + indS {s | s * b⁻¹ ∈ S} p + indS {s | s * (b ^ 2)⁻¹ ∈ S} p ≤ 1 := by
  have memL : ∀ {s c : SLR}, c ∈ Λ → s * c⁻¹ ∈ S → s ∈ Λ := fun {s c} hc h => by
    have := Λ.mul_mem (hSL h) hc
    rwa [inv_mul_cancel_right] at this
  have hb2 : b ^ 2 ∈ Λ := Λ.pow_mem hbL 2
  have d12 : ¬ (p ∈ grS S ∧ p ∈ grS {s | s * b⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * b⁻¹ ∈ S :=
      mul_mem_of_freeL hS hp (hSL hs) (memL hbL hs') (hsp.trans hs'p.symm) _ hs'
    exact (hb _ h1).1 (by rwa [inv_mul_cancel_right])
  have d13 : ¬ (p ∈ grS S ∧ p ∈ grS {s | s * (b ^ 2)⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * (b ^ 2)⁻¹ ∈ S :=
      mul_mem_of_freeL hS hp (hSL hs) (memL hb2 hs') (hsp.trans hs'p.symm) _ hs'
    exact (hb _ h1).2 (by rwa [inv_mul_cancel_right])
  have d23 : ¬ (p ∈ grS {s | s * b⁻¹ ∈ S} ∧ p ∈ grS {s | s * (b ^ 2)⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * (b ^ 2)⁻¹ ∈ S :=
      mul_mem_of_freeL hS hp (memL hbL hs) (memL hb2 hs') (hsp.trans hs'p.symm) _ hs'
    have h2 : s * (b ^ 2)⁻¹ * b = s * b⁻¹ := by group
    exact (hb _ h1).1 (by rw [h2]; exact hs)
  rw [indS_apply, indS_apply, indS_apply]
  split_ifs with h1 h2 h3 h3 h2 h3 h3
  · exact absurd ⟨h1, h2⟩ d12
  · exact absurd ⟨h1, h2⟩ d12
  · exact absurd ⟨h1, h3⟩ d13
  · norm_num
  · exact absurd ⟨h2, h3⟩ d23
  all_goals norm_num

lemma one_le_indS_two {S : Set SLR} {a : SLR}
    (ha : ∀ δ ∈ Λ, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * a ^ m ∈ S) {m : ℤ} (hm : m ≠ 0)
    (p : OnePoint ℝ × OnePoint ℝ) (hp : p ∈ relL Λ) :
    1 ≤ indS S p + indS {s | s * (a ^ m)⁻¹ ∈ S} p := by
  obtain ⟨g, hgL, hg⟩ := hp
  have h0 : ∀ T : Set SLR, 0 ≤ indS T p := fun T => by
    rw [indS_apply]; split_ifs <;> norm_num
  by_cases hgS : g ∈ S
  · have : indS S p = 1 := by rw [indS_apply, if_pos ⟨g, hgS, hg⟩]
    linarith [h0 {s | s * (a ^ m)⁻¹ ∈ S}]
  · have hmem : g * (a ^ m)⁻¹ ∈ S := by
      rw [← _root_.zpow_neg]; exact ha g hgL hgS (-m) (neg_ne_zero.2 hm)
    have : indS {s | s * (a ^ m)⁻¹ ∈ S} p = 1 := by rw [indS_apply, if_pos ⟨g, hmem, hg⟩]
    linarith [h0 S]

/-- The Carrière–Ghys contradiction for the orbit relation of a countable `Λ ≤ SL(2, ℝ)`. -/
theorem not_isAmenableRel_relL [Countable Λ] (a b : SLR) (haL : a ∈ Λ) (hbL : b ∈ Λ)
    (hnull : ∀ W : Set (OnePoint ℝ), NullMeasurableSet W volP1 →
      (∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (a ^ m) ⁻¹' W) = 0) → volP1 W = 0)
    (S : Set SLR) (hSL : S ⊆ Λ) (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S)
    (hb : ∀ δ ∈ S, δ * b ∉ S ∧ δ * b ^ 2 ∉ S)
    (ha : ∀ δ ∈ Λ, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * a ^ m ∈ S) :
    ¬ IsAmenableRel volP1 (relL Λ) := by
  rintro ⟨P, hP⟩
  have hLc : (Λ : Set SLR).Countable := Set.countable_coe_iff.1 ‹Countable Λ›
  have hcT : ∀ c ∈ Λ, ({s | s * c⁻¹ ∈ S} : Set SLR).Countable := fun c hc =>
    hLc.mono fun s hs => by
      have := Λ.mul_mem (hSL hs) hc
      rwa [inv_mul_cancel_right] at this
  have hSc : S.Countable := hLc.mono hSL
  set u := P (indS S) with hu_def
  have hbdd : ∀ T : Set SLR, T.Countable → IsBddMeasOn (relL Λ) (indS T) :=
    fun T hT => isBddMeasOn_indS _ hT
  have hb2 : b ^ 2 ∈ Λ := Λ.pow_mem hbL 2
  have hE1 : ∀ᵐ x ∂volP1, u x + u (mob b x) + u (mob (b ^ 2) x) ≤ 1 := by
    have hle := Monod.Dev.CG.A8.ae_le_of_le hP
      (Monod.Dev.CG.A8.isBddMeasOn_add (Monod.Dev.CG.A8.isBddMeasOn_add (hbdd S hSc)
        (hbdd _ (hcT b hbL))) (hbdd _ (hcT _ hb2)))
      (Monod.Dev.CG.A8.isBddMeasOn_one _) volP1_N0L
      (fun p _ hp => indS_three_le hSL hS hbL hb p hp)
    have h1 := hP.add _ _ (Monod.Dev.CG.A8.isBddMeasOn_add (hbdd S hSc) (hbdd _ (hcT b hbL)))
      (hbdd _ (hcT _ hb2))
    have h2 := hP.add _ _ (hbdd S hSc) (hbdd _ (hcT b hbL))
    have h3 := P_indS_shift hP hbL hSc
    have h4 := P_indS_shift hP hb2 hSc
    filter_upwards [hle, h1, h2, h3, h4, hP.one] with x hle h1 h2 h3 h4 h5
    simp only [Pi.add_apply, Function.comp_apply, Pi.one_apply] at hle h1 h2 h3 h4 h5
    linarith
  have hE2 : ∀ m : ℤ, m ≠ 0 → ∀ᵐ x ∂volP1, 1 ≤ u x + u (mob (a ^ m) x) := by
    intro m hm
    have ham : a ^ m ∈ Λ := Λ.zpow_mem haL m
    have hle := Monod.Dev.CG.A8.ae_le_of_le hP (Monod.Dev.CG.A8.isBddMeasOn_one _)
      (Monod.Dev.CG.A8.isBddMeasOn_add (hbdd S hSc) (hbdd _ (hcT _ ham))) (N := ∅)
      measure_empty (fun p hp _ => one_le_indS_two ha hm p hp)
    have h1 := hP.add _ _ (hbdd S hSc) (hbdd _ (hcT _ ham))
    have h3 := P_indS_shift hP ham hSc
    filter_upwards [hle, h1, h3, hP.one] with x hle h1 h3 h5
    simp only [Pi.add_apply, Function.comp_apply, Pi.one_apply] at hle h1 h3 h5
    linarith
  have hum : AEMeasurable u volP1 := hP.aemeasurable _ (hbdd S hSc)
  set W : Set (OnePoint ℝ) := {x | u x < 1 / 2} with hW_def
  have hWm : NullMeasurableSet W volP1 := hum.nullMeasurableSet_preimage measurableSet_Iio
  have hwand : ∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (a ^ m) ⁻¹' W) = 0 := by
    intro m hm
    refine measure_mono_null ?_ (ae_iff.1 (hE2 m hm))
    rintro x ⟨hx1, hx2⟩
    simp only [hW_def, Set.mem_ofPred_eq, Set.mem_preimage] at hx1 hx2 ⊢
    linarith
  have hW0 : volP1 W = 0 := hnull W hWm hwand
  have hgood : ∀ g : SLR, ∀ᵐ x ∂volP1, 1 / 2 ≤ u (mob g x) := by
    intro g
    rw [ae_iff]
    refine measure_mono_null ?_ (Monod.Dev.CG.A8.null_preimage_mob g hW0)
    intro x hx
    simp only [Set.mem_ofPred_eq, not_le] at hx
    exact hx
  have hfalse : ∀ᵐ x ∂volP1, False := by
    filter_upwards [hE1, hgood 1, hgood b, hgood (b ^ 2)] with x h1 h2 h3 h4
    rw [mob_one] at h2
    linarith
  rw [ae_iff] at hfalse
  simp only [not_false_eq_true, Set.ofPred_true] at hfalse
  rw [Monod.Dev.CG.A8.volP1_univ] at hfalse
  exact ENNReal.top_ne_zero hfalse

end CGL

/-! ## Elliptic elements -/

/-- The trace of an element of `SL(2, ℝ)`. -/
noncomputable def tr (a : SLR) : ℝ := ent a 0 0 + ent a 1 1

/-- `a` is elliptic of infinite order: `|tr a| < 2` and no nonzero power is `±1`. -/
def IsEllInf (a : SLR) : Prop := |tr a| < 2 ∧ ∀ m : ℤ, m ≠ 0 → a ^ m ≠ 1 ∧ a ^ m ≠ -1

/-- `x` and `y` freely generate a free group of rank two not containing `-1`. -/
def IsFreePair (x y : SLR) : Prop :=
  Function.Injective (FreeGroup.lift ![x, y]) ∧ (-1 : SLR) ∉ (FreeGroup.lift ![x, y]).range

lemma slMap_neg_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    SpecialLinearGroup.map (n := Fin 2) f (-1) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg]

lemma trace_slMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (g : SpecialLinearGroup (Fin 2) R) :
    ((SpecialLinearGroup.map f g : Matrix (Fin 2) (Fin 2) S)).trace =
      f ((g : Matrix (Fin 2) (Fin 2) R).trace) := by
  simp [Matrix.trace_fin_two]

/-! ### An elliptic element of infinite order, from `SL(2, ℝ)` -/

/-- The entrywise isomorphism `SL(2, ⊤) → SL(2, ℝ)`. -/
noncomputable abbrev toR : SLR →* SpecialLinearGroup (Fin 2) ℝ :=
  SpecialLinearGroup.map (Subring.topEquiv : (⊤ : Subring ℝ) ≃+* ℝ).toRingHom

lemma continuous_toR : Continuous toR :=
  Continuous.specialLinearGroup_map continuous_subtype_val

lemma toR_surjective : Function.Surjective toR := by
  intro g
  refine ⟨SpecialLinearGroup.map (Subring.topEquiv : (⊤ : Subring ℝ) ≃+* ℝ).symm.toRingHom g, ?_⟩
  ext i j
  simp

lemma dense_comap (Γ : Subgroup PSLR) (hΓ : Dense (Γ : Set PSLR)) :
    Dense ((Γ.comap pr : Subgroup SLR) : Set SLR) := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨g, hg, hgU⟩ := exists_mem_of_isOpen Γ hΓ hU hne
  exact ⟨g, hgU, hg⟩

theorem exists_ellInf (Γ : Subgroup PSLR) (hΓ : Dense (Γ : Set PSLR)) :
    ∃ a ∈ Γ.comap pr, IsEllInf a := by
  have hD : Dense (((Γ.comap pr).map toR : Subgroup (SpecialLinearGroup (Fin 2) ℝ)) :
      Set (SpecialLinearGroup (Fin 2) ℝ)) := by
    rw [Subgroup.coe_map]
    exact toR_surjective.denseRange.dense_image continuous_toR (dense_comap Γ hΓ)
  obtain ⟨a', ⟨a, haΓ, rfl⟩, htr, hpow⟩ := DenseSL2.exists_elliptic_infinite_order_of_dense _ hD
  refine ⟨a, haΓ, ?_, ?_⟩
  · have e : Matrix.trace (toR a : Matrix (Fin 2) (Fin 2) ℝ) = tr a := by
      rw [Matrix.trace_fin_two]; rfl
    rwa [e] at htr
  have key : ∀ n : ℕ, 0 < n → a ^ n ≠ 1 ∧ a ^ n ≠ -1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := hpow n hn
    refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
    · rw [← map_pow, h, map_one]
    · rw [← map_pow, h, slMap_neg_one]
  intro m hm
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact key n (by omega)
  · rw [_root_.zpow_neg, zpow_natCast]
    obtain ⟨h1, h2⟩ := key n (by omega)
    refine ⟨fun h => h1 (inv_eq_one.1 h), fun h => h2 ?_⟩
    rw [← inv_inv (a ^ n), h, inv_neg, inv_one]

/-! ### Elliptic elements are conservative -/

/-- Transport of the wandering-set property along a conjugation `a = P e P⁻¹`. -/
lemma null_of_wandering_conj (a e P : SLR) (hconj : P * e = a * P)
    (he : ∀ W : Set (OnePoint ℝ), NullMeasurableSet W volP1 →
      (∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (e ^ m) ⁻¹' W) = 0) → volP1 W = 0)
    (W : Set (OnePoint ℝ)) (hW : NullMeasurableSet W volP1)
    (hwand : ∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (a ^ m) ⁻¹' W) = 0) : volP1 W = 0 := by
  have qmp : Measure.QuasiMeasurePreserving (mob P) volP1 volP1 := by
    refine ⟨measurable_mob P, Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_⟩
    rw [Measure.map_apply (measurable_mob P) hS]
    exact null_preimage_mob P h0
  have ha : a = P * e * P⁻¹ := by rw [hconj]; group
  set W' := mob P ⁻¹' W with hW'
  have h' : volP1 W' = 0 := by
    refine he W' (hW.preimage qmp) fun m hm => ?_
    have hset : W' ∩ mob (e ^ m) ⁻¹' W' = mob P ⁻¹' (W ∩ mob (a ^ m) ⁻¹' W) := by
      ext x
      simp only [hW', Set.mem_inter_iff, Set.mem_preimage, ha, conj_zpow, mob_mul, mob_inv_mob]
    rw [hset]
    exact null_preimage_mob P (hwand m hm)
  have hWW : W = mob P⁻¹ ⁻¹' W' := by
    ext x
    simp only [hW', Set.mem_preimage, mob_mob_inv]
  rw [hWW]
  exact null_preimage_mob P⁻¹ h'

/-- An elliptic element whose lower-left entry is positive is conjugate to `ell (tr a)`. -/
lemma null_of_wandering_of_pos (a : SLR) (ha : |tr a| < 2) (hr : 0 < ent a 1 0)
    (W : Set (OnePoint ℝ)) (hW : NullMeasurableSet W volP1)
    (hwand : ∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (a ^ m) ⁻¹' W) = 0) : volP1 W = 0 := by
  set q := Real.sqrt (ent a 1 0) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hr
  have hqq : q * q = ent a 1 0 := Real.mul_self_sqrt hr.le
  set t : (⊤ : Subring ℝ) := ⟨tr a, trivial⟩ with ht
  set P : SLR := mk2 (ent a 0 0 / q) (-1 / q) q 0 (by field_simp; ring) with hP
  have hconj : P * Monod.Dev.CG.ell t = a * P := by
    obtain ⟨e1, e2, e3, e4⟩ := Monod.Dev.CG.A4.ell_apply t
    have f1 : ent (Monod.Dev.CG.ell t) 0 0 = tr a := e1
    have f2 : ent (Monod.Dev.CG.ell t) 0 1 = -1 := e2
    have f3 : ent (Monod.Dev.CG.ell t) 1 0 = 1 := e3
    have f4 : ent (Monod.Dev.CG.ell t) 1 1 = 0 := e4
    have hd := det_ent a
    apply slr_ext
    intro i j
    rw [ent_mul, ent_mul]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, f1, f2, f3, f4, hP, ent_mk2_00,
        ent_mk2_01, ent_mk2_10, ent_mk2_11, tr] <;> field_simp
    · linear_combination hd - ent a 0 1 * hqq
    · ring
    · linear_combination ent a 0 0 * hqq
    · linear_combination (-1 : ℝ) * hqq
  exact null_of_wandering_conj a _ P hconj
    (fun W hW hwand => Monod.Dev.CG.chk_null_of_wandering t (by simpa [ht] using ha) W hW hwand)
    W hW hwand

lemma tr_inv (a : SLR) : tr a⁻¹ = tr a := by
  rw [tr, tr, ent_inv_00, ent_inv_11, add_comm]

lemma ent_one_ne_zero_of_elliptic (a : SLR) (ha : |tr a| < 2) : ent a 1 0 ≠ 0 := by
  intro h0
  have hd := det_ent a
  rw [h0, mul_zero, sub_zero] at hd
  obtain ⟨h1, h2⟩ := abs_lt.mp ha
  unfold tr at h1 h2
  nlinarith [sq_nonneg (ent a 0 0 - ent a 1 1)]

theorem null_of_wandering_of_elliptic (a : SLR) (ha : |tr a| < 2) (W : Set (OnePoint ℝ))
    (hW : NullMeasurableSet W volP1)
    (hwand : ∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (a ^ m) ⁻¹' W) = 0) : volP1 W = 0 := by
  rcases (ent_one_ne_zero_of_elliptic a ha).lt_or_gt with hneg | hpos
  · refine null_of_wandering_of_pos a⁻¹ (by rwa [tr_inv]) ?_ W hW fun m hm => ?_
    · rw [ent_inv_10]; linarith
    · rw [_root_.inv_zpow']
      exact hwand (-m) (neg_ne_zero.2 hm)
  · exact null_of_wandering_of_pos a ha hpos W hW hwand

/-! ### Traces of powers of an elliptic element -/

/-- Cayley–Hamilton, entrywise: `a² = (tr a) a - 1`. -/
lemma ent_sq (a : SLR) (i j : Fin 2) :
    ent a i 0 * ent a 0 j + ent a i 1 * ent a 1 j =
      tr a * ent a i j - (if i = j then 1 else 0) := by
  have hd := det_ent a
  unfold tr
  fin_cases i <;> fin_cases j <;> simp <;>
    first | ring1 | linear_combination hd | linear_combination (-1 : ℝ) * hd

/-- Every power of `a` lies in the span of `a` and `1`. -/
lemma pow_eq_lin (a : SLR) (n : ℕ) :
    ∃ s u : ℝ, ∀ i j, ent (a ^ n) i j = s * ent a i j + u * (if i = j then 1 else 0) := by
  induction n with
  | zero => exact ⟨0, 1, fun i j => by rw [pow_zero, ent_one]; ring⟩
  | succ n ih =>
    obtain ⟨s, u, h⟩ := ih
    refine ⟨s * tr a + u, -s, fun i j => ?_⟩
    have hsq := ent_sq a i j
    rw [pow_succ, ent_mul, h, h]
    fin_cases i <;> fin_cases j <;> simp at hsq ⊢ <;> linear_combination s * hsq

theorem abs_tr_pow_lt (a : SLR) (ha : IsEllInf a) (N : ℕ) (hN : 0 < N) : |tr (a ^ N)| < 2 := by
  obtain ⟨s, u, h⟩ := pow_eq_lin a N
  have hd := det_ent a
  have hdN := det_ent (a ^ N)
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [Fin.isValue, if_true, if_false, zero_ne_one, one_ne_zero, mul_one, mul_zero,
    add_zero] at h00 h01 h10 h11
  rw [h00, h01, h10, h11] at hdN
  have htN : tr (a ^ N) = s * tr a + 2 * u := by
    rw [tr, tr, h00, h11]; ring
  have key : tr (a ^ N) ^ 2 - 4 = s ^ 2 * (tr a ^ 2 - 4) := by
    rw [htN]; unfold tr; linear_combination 4 * hdN - 4 * s ^ 2 * hd
  have ht2 : tr a ^ 2 < 4 := by
    obtain ⟨h1, h2⟩ := abs_lt.mp ha.1
    nlinarith
  rcases eq_or_ne s 0 with hs | hs
  · exfalso
    rw [hs] at h00 h01 h10 h11 hdN
    simp only [zero_mul, zero_add] at h00 h01 h10 h11 hdN
    have hu : (u - 1) * (u + 1) = 0 := by linear_combination hdN
    have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    obtain ⟨hne1, hne2⟩ := ha.2 N hNz
    rw [zpow_natCast] at hne1 hne2
    rcases mul_eq_zero.1 hu with hu | hu
    · apply hne1
      apply slr_ext
      intro i j
      rw [ent_one]
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11] <;> linarith
    · apply hne2
      apply slr_ext
      intro i j
      rw [ent_neg_one]
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11] <;> linarith
  · have hs2 : 0 < s ^ 2 := by positivity
    have : tr (a ^ N) ^ 2 < 2 ^ 2 := by nlinarith
    exact abs_lt_of_sq_lt_sq this (by norm_num)

/-! ## A free pair in `Γ̃` with first element a power of `a` -/

/-- The trace of the commutator `[a, c a c⁻¹]`. -/
noncomputable def ctr (a c : SLR) : ℝ := tr (a * (c * a * c⁻¹) * a⁻¹ * (c * a * c⁻¹)⁻¹)

lemma continuous_ent (i j : Fin 2) : Continuous (fun g : SLR => ent g i j) :=
  continuous_subtype_val.comp (continuous_subtype_val.matrix_elem i j)

lemma continuous_tr : Continuous tr :=
  (continuous_ent 0 0).add (continuous_ent 1 1)

lemma continuous_ctr (a : SLR) : Continuous (ctr a) := by
  have h1 : Continuous (fun c : SLR => c * a * c⁻¹) :=
    (continuous_id.mul continuous_const).mul continuous_inv
  exact continuous_tr.comp (((continuous_const.mul h1).mul continuous_const).mul h1.inv)

/-- The diagonal matrix `diag(2, 1/2)`. -/
noncomputable def c₀ : SLR := mk2 2 0 0 (1 / 2) (by norm_num)

/-- For an elliptic `a`, the commutator trace with `diag(2, 1/2)` is not `2`. -/
lemma ctr_c₀_ne (a : SLR) (ha : |tr a| < 2) : ctr a c₀ ≠ 2 := by
  have hdet := det_ent a
  set p := ent a 0 0
  set q := ent a 0 1
  set r := ent a 1 0
  set s := ent a 1 1
  have ht : (p + s) ^ 2 < 4 := by
    have : |p + s| < 2 := ha
    nlinarith [abs_lt.1 this]
  have hqr : q * r < 0 := by nlinarith [sq_nonneg (p - s)]
  have hE : ctr a c₀ - 2 =
      (9 / 4) * (q * r) * ((p + s) ^ 2 - 4 + (9 / 4) * (q * r)) := by
    simp only [ctr, tr, c₀, ent_mul, ent_inv_00, ent_inv_01, ent_inv_10, ent_inv_11, ent_mk2_00,
      ent_mk2_01, ent_mk2_10, ent_mk2_11]
    linear_combination (2 * p * s - 11 * q * r + 2) * hdet
  intro h
  rw [h, sub_self] at hE
  have : 0 < (9 / 4) * (q * r) * ((p + s) ^ 2 - 4 + (9 / 4) * (q * r)) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

/-! ### Traces of roots of unity force finite order -/

/-- The real matrix of an element of `SLR`. -/
noncomputable def rmat (g : SLR) : Matrix (Fin 2) (Fin 2) ℝ :=
  (⊤ : Subring ℝ).subtype.mapMatrix (g : Matrix (Fin 2) (Fin 2) (⊤ : Subring ℝ))

lemma rmat_apply (g : SLR) (i j : Fin 2) : rmat g i j = ent g i j := rfl

lemma rmat_pow (g : SLR) (n : ℕ) : rmat (g ^ n) = rmat g ^ n := by
  simp [rmat, Matrix.SpecialLinearGroup.coe_pow, map_pow]

/-- If `tr a = z + z⁻¹` with `z` a root of unity and `|tr a| < 2`, then `a ^ n = 1`. -/
lemma pow_eq_one_of_tr (a : SLR) (ha : |tr a| < 2) (z : ℂ) (n : ℕ) (hn : 0 < n)
    (hz : z ^ n = 1) (ht : (tr a : ℂ) = z + z⁻¹) : a ^ n = 1 := by
  classical
  set t := tr a with ht_def
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [zero_pow hn.ne'] at hz
  have hzz : z ≠ z⁻¹ := by
    intro h
    have h1 : z * z = 1 := by
      calc z * z = z * z⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hz0
    have h2 : (z - 1) * (z + 1) = 0 := by linear_combination h1
    have habs := abs_lt.1 ha
    rcases mul_eq_zero.1 h2 with h3 | h3
    · have : z = 1 := sub_eq_zero.1 h3
      subst this
      have : (t : ℂ) = ((2 : ℝ) : ℂ) := by rw [ht]; norm_num
      have := Complex.ofReal_injective this
      linarith
    · have : z = -1 := eq_neg_of_add_eq_zero_left h3
      subst this
      have : (t : ℂ) = ((-2 : ℝ) : ℂ) := by rw [ht]; norm_num
      have := Complex.ofReal_injective this
      linarith
  set P : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1 with hP
  have hPmap : P.map (algebraMap ℝ ℂ) =
      (Polynomial.X - Polynomial.C z) * (Polynomial.X - Polynomial.C z⁻¹) := by
    have hzi : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
    simp only [hP, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_one]
    have hC : Polynomial.C (algebraMap ℝ ℂ t) = Polynomial.C z + Polynomial.C z⁻¹ := by
      rw [← Polynomial.C_add]; congr 1
    have hC1 : (1 : Polynomial ℂ) = Polynomial.C z * Polynomial.C z⁻¹ := by
      rw [← Polynomial.C_mul, hzi, Polynomial.C_1]
    rw [hC, hC1]
    ring
  have hdvd : P ∣ Polynomial.X ^ n - 1 := by
    rw [← Polynomial.map_dvd_map' (algebraMap ℝ ℂ), hPmap]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    apply IsCoprime.mul_dvd
    · exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hzz).isUnit
    · rw [Polynomial.dvd_iff_isRoot]; simp [hz]
    · rw [Polynomial.dvd_iff_isRoot]; simp [inv_pow, hz]
  obtain ⟨Q, hQ⟩ := hdvd
  have hCH : rmat a ^ 2 - (t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * rmat a + 1 = 0 := by
    have hdet := det_ent a
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, Matrix.mul_apply, Fin.sum_univ_two, rmat_apply, ht_def, tr] <;>
      first | ring1 | linear_combination (-1 : ℝ) * hdet
  have hMn : rmat a ^ n = 1 := by
    have h := congrArg (Polynomial.aeval (rmat a)) hQ
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hP, map_add,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at h
    rw [hCH, zero_mul] at h
    exact sub_eq_zero.1 h
  apply slr_ext
  intro i j
  have := congrFun (congrFun hMn i) j
  rw [← rmat_pow, rmat_apply] at this
  rw [this, ent_one, Matrix.one_apply]

/-- `hinf` for an elliptic element of infinite order. -/
lemma hinf_of_isEllInf (a : SLR) (ha : IsEllInf a) :
    ∀ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → (tr a : ℂ) ≠ z + z⁻¹ := by
  rintro z ⟨n, hn, hz⟩ ht
  have h1 := pow_eq_one_of_tr a ha.1 z n hn hz ht
  have h2 := (ha.2 (n : ℤ) (by exact_mod_cast hn.ne')).1
  rw [zpow_natCast] at h2
  exact h2 h1

/-! ### Matrices with entries in a subfield of `ℝ` -/

section Sub

variable (K : Subfield ℝ)

/-- The inclusion of `K` into `⊤ : Subring ℝ`. -/
def fK : K →+* (⊤ : Subring ℝ) where
  toFun k := ⟨k.1, trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion `SL(2, K) → SL(2, ℝ)`. -/
noncomputable abbrev incl : SpecialLinearGroup (Fin 2) K →* SLR := SpecialLinearGroup.map (fK K)

lemma ent_incl (g : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    ent (incl K g) i j = ((g i j : K) : ℝ) := rfl

lemma incl_injective : Function.Injective (incl K) := by
  intro g h hgh
  ext i j
  have := congrArg (fun g => ent g i j) hgh
  simp only [ent_incl] at this
  exact this

/-- An element of `SLR` with entries in `K`, as an element of `SL(2, K)`. -/
noncomputable def liftK (g : SLR) (hg : ∀ i j, ent g i j ∈ K) : SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.of fun i j => ⟨ent g i j, hg i j⟩, by
    rw [Matrix.det_fin_two]
    apply Subtype.ext
    simpa using det_ent g⟩

lemma liftK_apply (g : SLR) (hg : ∀ i j, ent g i j ∈ K) (i j : Fin 2) :
    ((liftK K g hg i j : K) : ℝ) = ent g i j := rfl

lemma incl_liftK (g : SLR) (hg : ∀ i j, ent g i j ∈ K) : incl K (liftK K g hg) = g :=
  slr_ext fun _ _ => rfl

lemma tr_incl (g : SpecialLinearGroup (Fin 2) K) :
    tr (incl K g) = (((g : Matrix (Fin 2) (Fin 2) K).trace : K) : ℝ) := by
  simp [tr, ent_incl, Matrix.trace_fin_two]

lemma incl_neg_one : incl K (-1) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg, fK]

end Sub

/-- A free pair in `Γ̃` with first element a power of `a`: choose `c ∈ Γ̃` with
`tr [a, c a c⁻¹] ≠ 2` by density, embed the field generated by the entries of `a` and `c` into a
normed field where `a` becomes proximal (Tits), play ping-pong there, and pull the free pair back. -/
theorem exists_freePair (Γ : Subgroup PSLR) (hΓ : Dense (Γ : Set PSLR)) (a : SLR)
    (haΓ : a ∈ Γ.comap pr) (ha : IsEllInf a) :
    ∃ N : ℕ, 0 < N ∧ ∃ b ∈ Γ.comap pr, IsFreePair (a ^ N) b := by
  classical
  -- a conjugator `c ∈ Γ̃` with `tr [a, c a c⁻¹] ≠ 2`
  obtain ⟨c, hcΓ, hc⟩ := exists_mem_of_isOpen Γ hΓ
    (isOpen_ne_fun (continuous_ctr a) continuous_const) ⟨c₀, ctr_c₀_ne a ha.1⟩
  -- the field generated by the entries of `a` and `c`
  set s : Finset ℝ := Finset.image (fun p : Fin 2 × Fin 2 => ent a p.1 p.2) Finset.univ ∪
    Finset.image (fun p : Fin 2 × Fin 2 => ent c p.1 p.2) Finset.univ with hs
  set K := Subfield.closure (s : Set ℝ) with hK
  have haK : ∀ i j, ent a i j ∈ K := by
    intro i j
    apply Subfield.subset_closure
    rw [Finset.mem_coe, hs, Finset.mem_union]
    exact Or.inl (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  have hcK : ∀ i j, ent c i j ∈ K := by
    intro i j
    apply Subfield.subset_closure
    rw [Finset.mem_coe, hs, Finset.mem_union]
    exact Or.inr (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  have hts : tr a ∈ K := add_mem (haK 0 0) (haK 1 1)
  -- Tits
  obtain ⟨L, _, σ, μ, hμ, hμt⟩ :=
    TitsLemma.exists_ringHom_proximal s (tr a) hts (hinf_of_isEllInf a ha)
  set aK := liftK K a haK with haK_def
  set cK := liftK K c hcK with hcK_def
  set φ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) L :=
    SpecialLinearGroup.map σ with hφ
  set x := φ aK with hx_def
  set c' := φ cK with hc'_def
  have hσ : Function.Injective σ := σ.injective
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have h2K : (2 : K) ≠ 0 := by
      intro h'
      have : ((2 : K) : ℝ) = 0 := by rw [h']; rfl
      norm_num at this
    exact h2K (hσ (by rw [map_ofNat, h, map_zero]))
  have hx : μ + μ⁻¹ = (x : Matrix (Fin 2) (Fin 2) L).trace := by
    rw [hμt, hx_def, hφ, trace_slMap]
    congr 1
    apply Subtype.ext
    simp [Matrix.trace_fin_two, haK_def, liftK_apply, tr]
  have hcomm : ((x * (c' * x * c'⁻¹) * x⁻¹ * (c' * x * c'⁻¹)⁻¹ :
      SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).trace ≠ 2 := by
    have he : x * (c' * x * c'⁻¹) * x⁻¹ * (c' * x * c'⁻¹)⁻¹ =
        φ (aK * (cK * aK * cK⁻¹) * aK⁻¹ * (cK * aK * cK⁻¹)⁻¹) := by
      simp only [hx_def, hc'_def, map_mul, map_inv]
    rw [he, hφ, trace_slMap]
    intro h
    apply hc
    have hK2 : ((aK * (cK * aK * cK⁻¹) * aK⁻¹ * (cK * aK * cK⁻¹)⁻¹ :
        SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = 2 :=
      hσ (by rw [h, map_ofNat])
    have hincl : incl K (aK * (cK * aK * cK⁻¹) * aK⁻¹ * (cK * aK * cK⁻¹)⁻¹) =
        a * (c * a * c⁻¹) * a⁻¹ * (c * a * c⁻¹)⁻¹ := by
      simp only [map_mul, map_inv, haK_def, hcK_def, incl_liftK]
    show tr (a * (c * a * c⁻¹) * a⁻¹ * (c * a * c⁻¹)⁻¹) = 2
    rw [← hincl, tr_incl, hK2]
    rfl
  -- ping-pong
  obtain ⟨N, hN, hinj, hneg⟩ :=
    PingPongSL2.exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal h2 x c' μ hμ hx hcomm
  refine ⟨N, hN, c * a ^ N * c⁻¹, ?_, ?_⟩
  · exact mul_mem (mul_mem hcΓ (pow_mem haΓ N)) (inv_mem hcΓ)
  set FK := FreeGroup.lift ![aK ^ N, cK * aK ^ N * cK⁻¹] with hFK
  have hR : FreeGroup.lift ![a ^ N, c * a ^ N * c⁻¹] = (incl K).comp FK := by
    ext i
    fin_cases i <;> simp [hFK, haK_def, hcK_def, incl_liftK]
  have hL : FreeGroup.lift ![x ^ N, c' * x ^ N * c'⁻¹] = φ.comp FK := by
    ext i
    fin_cases i <;> simp [hFK, hx_def, hc'_def]
  refine ⟨?_, ?_⟩
  · intro w₁ w₂ hw
    rw [hR] at hw
    have h1 : FK w₁ = FK w₂ := incl_injective K hw
    apply hinj
    rw [hL]
    simp only [MonoidHom.comp_apply, h1]
  · rintro ⟨w, hw⟩
    rw [hR, MonoidHom.comp_apply, ← incl_neg_one K] at hw
    have h1 : FK w = -1 := incl_injective K hw
    apply hneg
    refine ⟨w, ?_⟩
    rw [hL, MonoidHom.comp_apply, h1, hφ, slMap_neg_one]

/-! ## The ping-pong set -/

/-! ### The last letter of a reduced word -/

/-- The generator of the last letter of the reduced word of `w` (`none` for `w = 1`). -/
def lastGen (w : FreeGroup (Fin 2)) : Option (Fin 2) := (w.toWord.getLast?).map Prod.fst

lemma isReduced_append_replicate {L : List (Fin 2 × Bool)} (hL : FreeGroup.IsReduced L)
    (i : Fin 2) (b : Bool) (n : ℕ) (hlast : (L.getLast?).map Prod.fst ≠ some i) :
    FreeGroup.IsReduced (L ++ List.replicate n (i, b)) := by
  refine List.IsChain.append hL (List.isChain_replicate_of_rel _ (fun _ => rfl)) ?_
  intro p hp q hq hpq
  exfalso
  apply hlast
  have hq' : q = (i, b) := List.eq_of_mem_replicate (List.mem_of_mem_head? hq)
  rw [hp]
  simp [hpq, hq']

lemma toWord_zpow_of (i : Fin 2) (m : ℤ) :
    ∃ b, (FreeGroup.of i ^ m).toWord = List.replicate m.natAbs (i, b) := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · exact ⟨true, by rw [zpow_natCast, FreeGroup.toWord_of_pow, Int.natAbs_natCast]⟩
  · refine ⟨false, ?_⟩
    rw [_root_.zpow_neg, zpow_natCast, FreeGroup.toWord_inv, FreeGroup.toWord_of_pow,
      Int.natAbs_neg, Int.natAbs_natCast]
    simp [FreeGroup.invRev]

lemma lastGen_mul_zpow (w : FreeGroup (Fin 2)) (i : Fin 2) (hw : lastGen w ≠ some i) (m : ℤ)
    (hm : m ≠ 0) : lastGen (w * FreeGroup.of i ^ m) = some i := by
  obtain ⟨b, hb⟩ := toWord_zpow_of i m
  rw [lastGen, FreeGroup.toWord_mul, hb,
    (isReduced_append_replicate FreeGroup.isReduced_toWord i b _ hw).reduce_eq]
  have hne : List.replicate m.natAbs (i, b) ≠ [] := by
    simpa [List.replicate_eq_nil_iff] using hm
  rw [List.getLast?_append_of_ne_nil _ hne]
  simp [List.getLast?_replicate, hm]

/-! ### The retraction onto the free group, modulo `±1` -/

section Retraction

variable {G : Type*} [Group G] [HasDistribNeg G] (φ : FreeGroup (Fin 2) →* G)

/-- The subgroup `±F`, `F = range φ`. -/
def pmF : Subgroup G where
  carrier := {γ | ∃ g, γ = φ g ∨ γ = -φ g}
  mul_mem' := by
    rintro a b ⟨g, rfl | rfl⟩ ⟨h, rfl | rfl⟩
    · exact ⟨g * h, Or.inl (map_mul φ g h).symm⟩
    · exact ⟨g * h, Or.inr (by rw [mul_neg, map_mul])⟩
    · exact ⟨g * h, Or.inr (by rw [neg_mul, map_mul])⟩
    · exact ⟨g * h, Or.inl (by rw [neg_mul_neg, map_mul])⟩
  one_mem' := ⟨1, Or.inl (map_one φ).symm⟩
  inv_mem' := by
    rintro a ⟨g, rfl | rfl⟩
    · exact ⟨g⁻¹, Or.inl (map_inv φ g).symm⟩
    · exact ⟨g⁻¹, Or.inr (by rw [inv_neg, map_inv])⟩

variable {φ}

lemma pm_unique (hinj : Function.Injective φ) (hneg : (-1 : G) ∉ φ.range) {u : G}
    {g g' : FreeGroup (Fin 2)} (hg : u = φ g ∨ u = -φ g) (hg' : u = φ g' ∨ u = -φ g') :
    g = g' := by
  have key : ∀ g g' : FreeGroup (Fin 2), φ g ≠ -φ g' := by
    intro g g' h
    apply hneg
    refine ⟨g'⁻¹ * g, ?_⟩
    rw [map_mul, h, map_inv, mul_neg, inv_mul_cancel]
  rcases hg with rfl | rfl <;> rcases hg' with h | h
  · exact hinj h
  · exact absurd h (key g g')
  · exact absurd h.symm (key g' g)
  · exact hinj (neg_injective h)

variable (φ)

/-- A left-coset representative of `γ · (±F)`. -/
noncomputable def rep (γ : G) : G := (QuotientGroup.mk γ : G ⧸ pmF φ).out

lemma rep_inv_mul_mem (γ : G) : (rep φ γ)⁻¹ * γ ∈ pmF φ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (pmF φ) γ
  rw [rep, hh, _root_.mul_inv_rev, inv_mul_cancel_right]
  exact inv_mem h.2

lemma rep_mul (γ f : G) (hf : f ∈ pmF φ) : rep φ (γ * f) = rep φ γ := by
  unfold rep
  congr 1
  rw [QuotientGroup.eq]
  simpa [mul_assoc] using inv_mem hf

/-- The retraction `κ`, with `γ = rep γ · (±φ (κ γ))`. -/
noncomputable def kappa (γ : G) : FreeGroup (Fin 2) := Classical.choose (rep_inv_mul_mem φ γ)

lemma kappa_spec (γ : G) :
    (rep φ γ)⁻¹ * γ = φ (kappa φ γ) ∨ (rep φ γ)⁻¹ * γ = -φ (kappa φ γ) :=
  Classical.choose_spec (rep_inv_mul_mem φ γ)

variable {φ}

lemma kappa_mul (hinj : Function.Injective φ) (hneg : (-1 : G) ∉ φ.range) (γ : G)
    (h : FreeGroup (Fin 2)) : kappa φ (γ * φ h) = kappa φ γ * h := by
  have hrep : rep φ (γ * φ h) = rep φ γ := rep_mul φ γ (φ h) ⟨h, Or.inl rfl⟩
  refine pm_unique hinj hneg (kappa_spec φ (γ * φ h)) ?_
  rw [hrep, ← mul_assoc, map_mul]
  rcases kappa_spec φ γ with e | e <;> rw [e]
  · exact Or.inl rfl
  · exact Or.inr (neg_mul _ _)

lemma kappa_neg (hinj : Function.Injective φ) (hneg : (-1 : G) ∉ φ.range) (γ : G) :
    kappa φ (-γ) = kappa φ γ := by
  have hrep : rep φ (-γ) = rep φ γ := by
    rw [← mul_neg_one]
    exact rep_mul φ γ (-1) ⟨1, Or.inr (by rw [map_one])⟩
  refine pm_unique hinj hneg (kappa_spec φ (-γ)) ?_
  rw [hrep, mul_neg]
  rcases kappa_spec φ γ with e | e <;> rw [e]
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

end Retraction

theorem exists_pingpong_set_of_isFreePair (H : Subgroup SLR) (x y : SLR) (hx : x ∈ H)
    (hneg : (-1 : SLR) ∈ H) (hfree : IsFreePair x y) :
    ∃ S ⊆ (H : Set SLR), (∀ γ, -γ ∈ S ↔ γ ∈ S) ∧ (∀ δ ∈ S, δ * y ∉ S ∧ δ * y ^ 2 ∉ S) ∧
      (∀ δ ∈ H, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * x ^ m ∈ S) := by
  obtain ⟨hinj, hnr⟩ := hfree
  set φ : FreeGroup (Fin 2) →* SLR := FreeGroup.lift ![x, y] with hφ
  have hφx : ∀ m : ℤ, φ (FreeGroup.of 0 ^ m) = x ^ m := fun m => by
    rw [map_zpow, hφ, FreeGroup.lift_apply_of]; rfl
  have hφy : ∀ m : ℤ, φ (FreeGroup.of 1 ^ m) = y ^ m := fun m => by
    rw [map_zpow, hφ, FreeGroup.lift_apply_of]; rfl
  have hnegH : ∀ γ, -γ ∈ H ↔ γ ∈ H := fun γ => by
    rw [← neg_one_mul]
    exact ⟨fun h => by simpa using H.mul_mem hneg h, fun h => H.mul_mem hneg h⟩
  refine ⟨{δ | δ ∈ H ∧ lastGen (kappa φ δ) = some 0}, fun δ hδ => hδ.1, ?_, ?_, ?_⟩
  · intro γ
    simp only [Set.mem_ofPred_eq, hnegH, kappa_neg hinj hnr]
  · rintro δ ⟨-, hδ⟩
    have h1 : lastGen (kappa φ δ) ≠ some 1 := by rw [hδ]; decide
    refine ⟨?_, ?_⟩ <;> rintro ⟨-, h⟩
    · rw [← zpow_one y, ← hφy, kappa_mul hinj hnr,
        lastGen_mul_zpow _ _ h1 _ one_ne_zero] at h
      exact absurd h (by decide)
    · rw [← zpow_natCast, ← hφy, kappa_mul hinj hnr,
        lastGen_mul_zpow _ _ h1 _ (by norm_num)] at h
      exact absurd h (by decide)
  · intro δ hδH hδS m hm
    have h0 : lastGen (kappa φ δ) ≠ some 0 := fun h => hδS ⟨hδH, h⟩
    refine ⟨H.mul_mem hδH (H.zpow_mem hx m), ?_⟩
    rw [← hφx, kappa_mul hinj hnr]
    exact lastGen_mul_zpow _ _ h0 _ hm

/-! ## Assembly -/

/-- The preimage `Γ̃` of a dense `Γ ≤ PSL(2, ℝ)` contains a conservative `a`, an element `b` and a
ping-pong set `S` for right multiplication by `a` and `b`. -/
theorem exists_pingpong_of_dense (Γ : Subgroup PSLR) (hΓ : Dense (Γ : Set PSLR)) :
    ∃ a ∈ Γ.comap pr, ∃ b ∈ Γ.comap pr,
      (∀ W : Set (OnePoint ℝ), NullMeasurableSet W volP1 →
        (∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (a ^ m) ⁻¹' W) = 0) → volP1 W = 0) ∧
      ∃ S ⊆ (Γ.comap pr : Set SLR), (∀ γ, -γ ∈ S ↔ γ ∈ S) ∧
        (∀ δ ∈ S, δ * b ∉ S ∧ δ * b ^ 2 ∉ S) ∧
        (∀ δ ∈ Γ.comap pr, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * a ^ m ∈ S) := by
  obtain ⟨a₀, ha₀Γ, ha₀⟩ := exists_ellInf Γ hΓ
  obtain ⟨N, hN, b, hbΓ, hfree⟩ := exists_freePair Γ hΓ a₀ ha₀Γ ha₀
  obtain ⟨S, hSH, hS, hbS, haS⟩ := exists_pingpong_set_of_isFreePair (Γ.comap pr) (a₀ ^ N) b
    (pow_mem ha₀Γ N) (neg_one_mem_comap Γ) hfree
  exact ⟨a₀ ^ N, pow_mem ha₀Γ N, b, hbΓ,
    fun W hW hwand => null_of_wandering_of_elliptic (a₀ ^ N) (abs_tr_pow_lt a₀ ha₀ N hN) W hW hwand,
    S, hSH, hS, hbS, haS⟩

theorem not_isAmenableRel_orbit_of_dense
    (Γ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ))) [Countable Γ]
    (hΓ : Dense (Γ : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)))) :
    ¬ Monod.IsAmenableRel Monod.volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ A : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
        (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) ∈ Γ ∧
          Monod.mob A p.1 = p.2} := by
  have := countable_comap Γ
  obtain ⟨a, ha, b, hb, hnull, S, hSL, hS, hbS, haS⟩ := exists_pingpong_of_dense Γ hΓ
  exact not_isAmenableRel_relL a b ha hb hnull S hSL hS hbS haS

end CarriereGhys

end
end

section
open CarriereGhys

theorem solution
    (Γ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ))) [Countable Γ]
    (hΓ : Dense (Γ : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)))) :
    ¬ Monod.IsAmenableRel Monod.volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ A : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
        (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) ∈ Γ ∧
          Monod.mob A p.1 = p.2} := by
  apply CarriereGhys.not_isAmenableRel_orbit_of_dense <;> assumption

end
