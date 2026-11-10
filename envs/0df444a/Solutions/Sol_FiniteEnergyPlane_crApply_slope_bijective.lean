-- Prove2me | solution 1 for FiniteEnergyPlane.crApply_slope_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T22:44:36.527298+00:00
-- url     : https://prove2.me/submissions/5b44568c-8b99-4e01-a746-4148eabbddbd

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_isNondegenerate_const_smul_one
import Theorems.Thm_FiniteEnergyPlane_crIndex_slope_eq_zero
import Theorems.Thm_FiniteEnergyPlane_crApply_slope_injective
import Theorems.Thm_CauchyRiemannIndex_index_formula



/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-- `χ` is smooth with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`. -/
def IsSlopeWeight (χ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ (∀ s ≤ -1, deriv χ s = a) ∧ ∀ s ≥ 1, deriv χ s = b

/-! ### Slope weights are affine near the ends -/

theorem IsSlopeWeight.eq_right {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : 1 ≤ s) : χ s = χ 1 + b * (s - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have hb : deriv χ c = b := h.2.2 c hc.1.le
  rw [hb, eq_div_iff (by linarith)] at hc'
  linarith

theorem IsSlopeWeight.eq_left {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : s ≤ -1) : χ s = χ (-1) + a * (s + 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have ha : deriv χ c = a := h.2.1 c hc.2.le
  rw [ha, eq_div_iff (by linarith)] at hc'
  linarith


end FiniteEnergyPlane

/-!
# The slope coefficient `χ'(s) • 1` is asymptotic to constant loops (local helper)
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Tg-As: the slope coefficient is asymptotic to constant loops -/

lemma deriv_slope_bdd {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) :
    ∃ K, ∀ s, |deriv χ s| ≤ K := by
  have hc : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B (max |a| |b|), fun s => ?_⟩
  rcases le_or_gt s (-1) with h | h
  · rw [hχ.2.1 s h]; exact (le_max_left _ _).trans (le_max_right _ _)
  rcases le_or_gt 1 s with h' | h'
  · rw [hχ.2.2 s h']; exact (le_max_right _ _).trans (le_max_right _ _)
  · have := hB s ⟨h.le, h'.le⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- The homotopy `(1 - τ) χ'(s) + τ c`. -/
def slopeHom (χ : ℝ → ℝ) (c : ℝ) (τ : unitInterval) (x : ℝ × ℝ) : Mat 1 :=
  ((1 - (τ : ℝ)) * deriv χ x.1 + (τ : ℝ) * c) • (1 : Mat 1)

lemma slopeHom_isAsymptoticTo {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) (c : ℝ)
    (τ : unitInterval) :
    IsAsymptoticTo (slopeHom χ c τ) (fun _ => ((1 - (τ : ℝ)) * b + (τ : ℝ) * c) • (1 : Mat 1))
      (fun _ => ((1 - (τ : ℝ)) * a + (τ : ℝ) * c) • (1 : Mat 1)) := by
  have hc : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  refine ⟨?_, fun s t => rfl, fun ε hε => ⟨1, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩⟩
  · unfold slopeHom
    exact ((continuous_const.mul (hc.comp continuous_fst)).add continuous_const).smul
      continuous_const
  · simp only [slopeHom, hχ.2.2 s hs, sub_self, abs_zero]; exact hε.le
  · simp only [slopeHom, hχ.2.1 s hs, sub_self, abs_zero]; exact hε.le

lemma convex_mem {a c : ℝ} (ha : a ∈ Ioo 0 (2 * π)) (hc : c ∈ Ioo 0 (2 * π))
    (τ : unitInterval) : (1 - (τ : ℝ)) * a + (τ : ℝ) * c ∈ Ioo 0 (2 * π) := by
  have h0 : 0 ≤ (τ : ℝ) := τ.2.1
  have h1 : (τ : ℝ) ≤ 1 := τ.2.2
  have hm : 0 < min a c := lt_min ha.1 hc.1
  have hM : max a c < 2 * π := max_lt ha.2 hc.2
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (min_le_left a c)),
      mul_nonneg h0 (sub_nonneg.2 (min_le_right a c))]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_max_left a c)),
      mul_nonneg h0 (sub_nonneg.2 (le_max_right a c))]

end

end FiniteEnergyPlane

/-!
# Q-Tg glue (local, NOT published)

* Tg-Inj `crApply_slope_injective` (from `Scratch/JWQ_TgInj5`).
* glue `crApply_slope_bijective_proof`: Fredholm (index formula) + index `0` (`JWQ_Tg`) +
  injective ⇒ onto.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Glue -/

lemma crApply_add_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1) (v w : Triple 1 p) :
    crApply S (v + w) =ᵐ[cylMeasure] crApply S v + crApply S w := by
  filter_upwards [Lp.coeFn_add v.1 w.1, Lp.coeFn_add v.2.1 w.2.1, Lp.coeFn_add v.2.2 w.2.2]
    with x h1 h2 h3
  simp only [crApply, Prod.fst_add, Prod.snd_add, Pi.add_apply, h1, h2, h3, map_add]
  abel

lemma crApply_smul_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1) (r : ℝ) (w : Triple 1 p) :
    crApply S (r • w) =ᵐ[cylMeasure] r • crApply S w := by
  filter_upwards [Lp.coeFn_smul r w.1, Lp.coeFn_smul r w.2.1, Lp.coeFn_smul r w.2.2]
    with x h1 h2 h3
  simp only [crApply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, h1, h2, h3, map_smul,
    smul_add]

lemma crApply_zero_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1) :
    crApply S (0 : Triple 1 p) =ᵐ[cylMeasure] 0 := by
  filter_upwards [Lp.coeFn_zero (Vec 1) p cylMeasure] with x h
  simp only [crApply, Prod.fst_zero, Prod.snd_zero, h, Pi.zero_apply, map_zero, add_zero]

/-- Every element of `crRange` is an image. -/
lemma mem_crRange_iff (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1) (f : LpCyl 1 p)
    (hf : f ∈ crRange p S) :
    ∃ w ∈ W1p p 1, (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply S w := by
  induction hf using Submodule.span_induction with
  | mem f hf => exact hf
  | zero =>
    refine ⟨0, (W1p p 1).zero_mem, ?_⟩
    filter_upwards [Lp.coeFn_zero (Vec 1) p cylMeasure, crApply_zero_ae p S] with x h1 h2
    rw [h1, h2]
  | add f g _ _ hf hg =>
    obtain ⟨v, hv, hfv⟩ := hf
    obtain ⟨w, hw, hgw⟩ := hg
    refine ⟨v + w, (W1p p 1).add_mem hv hw, ?_⟩
    filter_upwards [Lp.coeFn_add f g, hfv, hgw, crApply_add_ae p S v w] with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, Pi.add_apply, h2, h3]
  | smul r f _ hf =>
    obtain ⟨v, hv, hfv⟩ := hf
    refine ⟨r • v, (W1p p 1).smul_mem r hv, ?_⟩
    filter_upwards [Lp.coeFn_smul r f, hfv, crApply_smul_ae p S r v] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, Pi.smul_apply, h2]

/-- Q-Tg, from Tg-Ix, Tg-Inj and the index formula. -/
theorem crApply_slope_bijective_proof (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (a b : ℝ) (ha : a ∈ Set.Ioo 0 (2 * π)) (hb : b ∈ Set.Ioo 0 (2 * π))
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ a b) :
    (∀ w ∈ W1p p 1, crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0 → w = 0) ∧
      ∀ f : LpCyl 1 p, ∃ w ∈ W1p p 1,
        (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w := by
  set S : ℝ × ℝ → Mat 1 := fun x => deriv χ x.1 • (1 : Mat 1) with hSdef
  have hinj := crApply_slope_injective p hp hp' a b ha hb χ hχ.1 hχ.2.1 hχ.2.2
  refine ⟨hinj, fun f => ?_⟩
  have hb' := isNondegenerate_const_smul_one 1 b hb
  have ha' := isNondegenerate_const_smul_one 1 a ha
  have hAs : IsAsymptoticTo S (fun _ => b • (1 : Mat 1)) (fun _ => a • (1 : Mat 1)) := by
    have := slopeHom_isAsymptoticTo hχ a 0
    have e : slopeHom χ a 0 = S := by funext x; simp [slopeHom, hSdef]
    simpa [e] using this
  obtain ⟨hF, -⟩ := index_formula 1 p hp hp' _ _ hb'.1 ha'.1 S hAs hb'.2 ha'.2
  have hI := crIndex_slope_eq_zero p hp hp' a b ha hb χ hχ.1 hχ.2.1 hχ.2.2
  have hk : crKernel p S = ⊥ := by
    refine (Submodule.span_eq_bot).2 fun w hw => hinj w hw.1 hw.2
  have hI' := hI
  rw [crIndex, hk, finrank_bot] at hI'
  haveI := hF.2.2
  have hq : Module.finrank ℝ (LpCyl 1 p ⧸ crRange p S) = 0 := by
    have : ((Module.finrank ℝ (LpCyl 1 p ⧸ crRange p S) : ℕ) : ℤ) = 0 := by
      push_cast at hI'; linarith
    exact_mod_cast this
  have hsub : Subsingleton (LpCyl 1 p ⧸ crRange p S) :=
    Module.finrank_zero_iff.1 hq
  have hr : crRange p S = ⊤ := Submodule.Quotient.subsingleton_iff.1 hsub
  exact mem_crRange_iff p S f (hr ▸ Submodule.mem_top)

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (a b : ℝ) (ha : a ∈ Ioo 0 (2 * π)) (hb : b ∈ Ioo 0 (2 * π))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχa : ∀ s ≤ -1, deriv χ s = a)
    (hχb : ∀ s ≥ 1, deriv χ s = b) :
    (∀ w ∈ W1p p 1, crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0 → w = 0) ∧
      ∀ f : LpCyl 1 p, ∃ w ∈ W1p p 1,
        (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w :=
  FiniteEnergyPlane.crApply_slope_bijective_proof p hp hp' a b ha hb χ ⟨hχ, hχa, hχb⟩
