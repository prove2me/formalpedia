-- Prove2me | solution 1 for DbarRegularity.eLpNorm_integral_mul_sub_le_of_hormander
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:04:45.062183+00:00
-- url     : https://prove2.me/submissions/39206a37-95e9-44a6-823e-bb772dd56a96

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_eLpNorm_integral_mul_sub_le_of_hormander_of_lt_two
import Theorems.Thm_DbarRegularity_integral_integral_mul_sub_mul_comm
import Theorems.Thm_DbarRegularity_eLpNorm_le_of_forall_enorm_integral_mul_le
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique



namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

/-- `L^p` bound, `1 < p < ∞`, on `L¹ ∩ L^p` for convolution with an `L²` kernel `K` on `ℝ^d` that
satisfies the Hörmander condition with constant `B₁` and is bounded on `L²` with norm `B₂`; the
constant depends only on `d`, `p`, `B₁`, `B₂`. -/
theorem eLpNorm_integral_mul_sub_le_of_hormander {d : ℕ} (hd : 0 < d) (p : ℝ) (hp : 1 < p)
    (B₁ B₂ : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ K : EuclideanSpace ℝ (Fin d) → ℂ, MemLp K 2 volume →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      ∀ f, Integrable f volume → MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume ≤
          A * eLpNorm f (ENNReal.ofReal p) volume := by
  -- the reflected kernel satisfies the same bounds
  have hrefl : ∀ K : EuclideanSpace ℝ (Fin d) → ℂ, MemLp K 2 volume →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      MemLp (fun z => K (-z)) 2 volume ∧
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (-(x - y)) - K (-x)‖ₑ ≤ B₁) ∧
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (-(x - y)) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) := by
    intro K hK hH hL2
    refine ⟨hK.comp_measurePreserving (Measure.measurePreserving_neg volume), ?_, ?_⟩
    · intro y hy
      have h := hH (-y) (neg_ne_zero.2 hy)
      rw [norm_neg] at h
      have hS : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | 2 * ‖y‖ ≤ ‖x‖} :=
        measurableSet_le measurable_const measurable_norm
      rw [← lintegral_indicator hS] at h ⊢
      rw [← lintegral_neg_eq_self]
      refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) h
      by_cases hx : 2 * ‖y‖ ≤ ‖x‖
      · rw [indicator_of_mem (show -x ∈ {x | 2 * ‖y‖ ≤ ‖x‖} by simpa using hx),
          indicator_of_mem (show x ∈ {x : EuclideanSpace ℝ (Fin d) | 2 * ‖y‖ ≤ ‖x‖} from hx),
          show -(-x - y) = x - -y by abel, neg_neg]
      · rw [indicator_of_notMem (show -x ∉ {x | 2 * ‖y‖ ≤ ‖x‖} by simpa using hx),
          indicator_of_notMem (show x ∉ {x : EuclideanSpace ℝ (Fin d) | 2 * ‖y‖ ≤ ‖x‖} from hx)]
    · intro g hg
      have hg' : MemLp (fun y => g (-y)) 2 volume :=
        hg.comp_measurePreserving (Measure.measurePreserving_neg volume)
      have hu := aestronglyMeasurable_integral_mul_sub K _ hK.1 hg'.1
      have heq : (fun x => ∫ y, K (-(x - y)) * g y) =
          fun x => (fun x => ∫ y, K (x - y) * g (-y)) (-x) := by
        funext x
        simp only
        rw [← integral_neg_eq_self]
        congr 1; funext y
        rw [show -(x - -y) = -x - y by abel]
      rw [heq]
      calc eLpNorm (fun x => (fun x => ∫ y, K (x - y) * g (-y)) (-x)) 2 volume
          = eLpNorm (fun x => ∫ y, K (x - y) * g (-y)) 2 volume :=
            eLpNorm_comp_measurePreserving hu (Measure.measurePreserving_neg volume)
        _ ≤ B₂ * eLpNorm (fun y => g (-y)) 2 volume := hL2 _ hg'
        _ = B₂ * eLpNorm g 2 volume := by
            rw [show (fun y => g (-y)) = g ∘ Neg.neg from rfl,
              eLpNorm_comp_measurePreserving hg.1 (Measure.measurePreserving_neg volume)]
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · obtain ⟨A, hA⟩ := eLpNorm_integral_mul_sub_le_of_hormander_of_lt_two hd (ENNReal.ofReal p)
      (ENNReal.one_lt_ofReal.2 hp)
      (by rw [← ENNReal.ofReal_ofNat 2]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hp2)
      B₁ B₂
    exact ⟨A, fun K hK hH hL2 f _ hf => hA K hK hH hL2 f hf⟩
  · refine ⟨B₂, fun K hK hH hL2 f _ hf => ?_⟩
    rw [ENNReal.ofReal_ofNat] at hf ⊢
    exact hL2 f hf
  · set q := p / (p - 1) with hq
    have hq1 : 1 < q := by rw [hq, lt_div_iff₀ (by linarith)]; linarith
    have hq2 : q < 2 := by rw [hq, div_lt_iff₀ (by linarith)]; linarith
    obtain ⟨A, hA⟩ := eLpNorm_integral_mul_sub_le_of_hormander_of_lt_two hd (ENNReal.ofReal q)
      (ENNReal.one_lt_ofReal.2 hq1)
      (by rw [← ENNReal.ofReal_ofNat 2]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hq2)
      B₁ B₂
    refine ⟨A, fun K hK hH hL2 f hf1 hf => ?_⟩
    obtain ⟨hK', hH', hL2'⟩ := hrefl K hK hH hL2
    have hpq : q.HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
    refine eLpNorm_le_of_forall_enorm_integral_mul_le
      (aestronglyMeasurable_integral_mul_sub K f hK.1 hf1.1) hp hq _ ?_
    intro g hg
    have hg2 : MemLp g 2 volume := hg 2 (by norm_num)
    have hgq : MemLp g (ENNReal.ofReal q) volume :=
      hg _ (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le)
    set v : EuclideanSpace ℝ (Fin d) → ℂ := fun y => ∫ x, K (-(y - x)) * g x with hv
    have hT : ∫ x, (∫ y, K (x - y) * f y) * g x = ∫ y, v y * f y := by
      rw [integral_integral_mul_sub_mul_comm hK hf1 hg2]
      congr 1; funext y; simp only [hv, neg_sub]
    have hvq : eLpNorm v (ENNReal.ofReal q) volume ≤ A * eLpNorm g (ENNReal.ofReal q) volume :=
      hA (fun z => K (-z)) hK' hH' hL2' g hgq
    have hvm : AEStronglyMeasurable v volume :=
      aestronglyMeasurable_integral_mul_sub (fun z => K (-z)) g hK'.1 hg2.1
    have hq0 : ENNReal.ofReal q ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hp0 : ENNReal.ofReal p ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
    have holder : ∫⁻ y, ‖v y‖ₑ * ‖f y‖ₑ ≤
        eLpNorm v (ENNReal.ofReal q) volume * eLpNorm f (ENNReal.ofReal p) volume := by
      have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hvm.enorm hf.1.enorm
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
      simpa only [Pi.mul_apply] using h
    calc ‖∫ x, (∫ y, K (x - y) * f y) * g x‖ₑ = ‖∫ y, v y * f y‖ₑ := by rw [hT]
      _ ≤ ∫⁻ y, ‖v y‖ₑ * ‖f y‖ₑ :=
          (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_mul]))
      _ ≤ eLpNorm v (ENNReal.ofReal q) volume * eLpNorm f (ENNReal.ofReal p) volume := holder
      _ ≤ (A * eLpNorm g (ENNReal.ofReal q) volume) * eLpNorm f (ENNReal.ofReal p) volume := by
          gcongr
      _ = (A * eLpNorm f (ENNReal.ofReal p) volume) * eLpNorm g (ENNReal.ofReal q) volume := by
          ring

end DbarRegularity

open DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

theorem solution {d : ℕ} (hd : 0 < d) (p : ℝ) (hp : 1 < p)
    (B₁ B₂ : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ K : EuclideanSpace ℝ (Fin d) → ℂ, MemLp K 2 volume →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      ∀ f, Integrable f volume → MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y, K (x - y) * f y) (ENNReal.ofReal p) volume ≤
          A * eLpNorm f (ENNReal.ofReal p) volume :=
  eLpNorm_integral_mul_sub_le_of_hormander hd p hp B₁ B₂
