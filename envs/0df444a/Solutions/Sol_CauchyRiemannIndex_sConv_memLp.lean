-- Prove2me | solution 1 for CauchyRiemannIndex.sConv_memLp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T08:42:48.074473+00:00
-- url     : https://prove2.me/submissions/7bcb9eb7-f64c-4e43-8da7-c771bfb6c05b

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space

-- ===== Scratch/CRSConvBase.lean =====
/-!
# Convolution in `s` on the cylinder: shifts, Tonelli, measurability

`G(s, t) = ∫ ρ(σ) g(s - σ, t) dσ`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma sca_cyl_eq_prod :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

instance sca_sFinite : SFinite cylMeasure := by unfold cylMeasure; infer_instance

lemma sca_mp (a : ℝ) :
    MeasurePreserving (fun x : ℝ × ℝ => (x.1 - a, x.2)) cylMeasure cylMeasure := by
  have h := (measurePreserving_sub_right (volume : Measure ℝ) a).prod
    (MeasurePreserving.id (volume.restrict (Set.Ico (0 : ℝ) 1)))
  rw [sca_cyl_eq_prod]
  convert h using 1
  funext x
  rfl

lemma sca_me (a : ℝ) : MeasurableEmbedding (fun x : ℝ × ℝ => (x.1 - a, x.2)) :=
  ((MeasurableEquiv.subRight a).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding

lemma sca_meas_shift : Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.1 - p.2, p.1.2)) := by
  fun_prop

/-- Tonelli for `s`-shifts on the cylinder. -/
lemma sca_tonelli {k : ℝ → ℝ≥0∞} (hk : Measurable k) {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, (∫⁻ σ, k σ * h (x.1 - σ, x.2)) ∂cylMeasure =
      (∫⁻ σ, k σ) * ∫⁻ x, h x ∂cylMeasure := by
  rw [lintegral_lintegral_swap ((hk.comp measurable_snd).mul (hh.comp sca_meas_shift)).aemeasurable]
  have h1 : ∀ σ : ℝ, ∫⁻ x, k σ * h (x.1 - σ, x.2) ∂cylMeasure = k σ * ∫⁻ x, h x ∂cylMeasure := by
    intro σ
    rw [lintegral_const_mul (k σ) (f := fun x : ℝ × ℝ => h (x.1 - σ, x.2))
      (hh.comp ((measurable_fst.sub_const σ).prodMk measurable_snd))]
    congr 1
    exact (sca_mp σ).lintegral_comp hh
  simp_rw [h1]
  rw [lintegral_mul_const _ hk]

lemma sca_sm {g : ℝ × ℝ → Vec n} (hg : StronglyMeasurable g) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    StronglyMeasurable (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) := by
  have : StronglyMeasurable
      (Function.uncurry fun (x : ℝ × ℝ) (σ : ℝ) => ρ σ • g (x.1 - σ, x.2)) :=
    (hρ.measurable.comp measurable_snd).stronglyMeasurable.smul (hg.comp_measurable sca_meas_shift)
  exact this.integral_prod_right

lemma sca_enorm_le (g : ℝ × ℝ → Vec n) (ρ : ℝ → ℝ) (x : ℝ × ℝ) :
    ‖∫ σ, ρ σ • g (x.1 - σ, x.2)‖ₑ ≤ ∫⁻ σ, ‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1
  funext σ
  rw [enorm_smul]

end

end CauchyRiemannIndex

-- ===== Scratch/CRSConvLp.lean =====
/-!
# `G(s, t) = ∫ ρ(σ) g(s - σ, t) dσ` lies in `L^q`

Hölder bound `|G|^q ≤ ‖ρ‖₁^{q-1} ∫ |ρ| |g(· - σ)|^q`, then the shift Tonelli identity.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Hölder with weight `a`: `(∫ a b)^q ≤ (∫ a)^{q-1} ∫ a b^q`. -/
lemma sca_jensen {q : ℝ} (hq : 1 ≤ q) {a b : ℝ → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ σ, a σ * b σ) ^ q ≤ (∫⁻ σ, a σ) ^ (q - 1) * ∫⁻ σ, a σ * b σ ^ q := by
  have hq0 : 0 < q := by linarith
  have hi0 : 0 ≤ q⁻¹ := inv_nonneg.2 hq0.le
  have hi1 : 0 ≤ 1 - q⁻¹ := by
    have : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
    linarith
  have key := ENNReal.lintegral_mul_norm_pow_le (μ := (volume : Measure ℝ))
    (f := fun σ => a σ * b σ ^ q) (g := a) (ha.mul (hb.pow_const q)).aemeasurable ha.aemeasurable hi0 hi1 (by ring)
  have hpt : ∀ σ, (a σ * b σ ^ q) ^ q⁻¹ * a σ ^ (1 - q⁻¹) = a σ * b σ := by
    intro σ
    rw [ENNReal.mul_rpow_of_nonneg _ _ hi0, ENNReal.rpow_rpow_inv hq0.ne', mul_comm (a σ ^ q⁻¹),
      mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hi0 hi1,
      show q⁻¹ + (1 - q⁻¹) = (1 : ℝ) by ring, ENNReal.rpow_one, mul_comm]
  rw [show (fun σ => (a σ * b σ ^ q) ^ q⁻¹ * a σ ^ (1 - q⁻¹)) = fun σ => a σ * b σ from
    funext hpt] at key
  calc (∫⁻ σ, a σ * b σ) ^ q
      ≤ ((∫⁻ σ, a σ * b σ ^ q) ^ q⁻¹ * (∫⁻ σ, a σ) ^ (1 - q⁻¹)) ^ q :=
        ENNReal.rpow_le_rpow key hq0.le
    _ = (∫⁻ σ, a σ) ^ (q - 1) * ∫⁻ σ, a σ * b σ ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one, mul_comm]
        congr 2
        field_simp

lemma sca_lintegral_le {q : ℝ} (hq : 1 ≤ q) {g : ℝ × ℝ → Vec n} (hg : StronglyMeasurable g)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    ∫⁻ x, ‖∫ σ, ρ σ • g (x.1 - σ, x.2)‖ₑ ^ q ∂cylMeasure ≤
      (∫⁻ σ, ‖ρ σ‖ₑ) ^ (q - 1) * ((∫⁻ σ, ‖ρ σ‖ₑ) * ∫⁻ x, ‖g x‖ₑ ^ q ∂cylMeasure) := by
  have hq0 : 0 ≤ q := by linarith
  have hρm : Measurable fun σ => ‖ρ σ‖ₑ := hρ.measurable.enorm
  have hgm : Measurable fun x => ‖g x‖ₑ ^ q := hg.measurable.enorm.pow_const q
  calc ∫⁻ x, ‖∫ σ, ρ σ • g (x.1 - σ, x.2)‖ₑ ^ q ∂cylMeasure
      ≤ ∫⁻ x, (∫⁻ σ, ‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ) ^ q ∂cylMeasure :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (sca_enorm_le g ρ x) hq0
    _ ≤ ∫⁻ x, (∫⁻ σ, ‖ρ σ‖ₑ) ^ (q - 1) *
          (∫⁻ σ, ‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ ^ q) ∂cylMeasure :=
        lintegral_mono fun (x : ℝ × ℝ) => sca_jensen hq hρm
          (b := fun σ => ‖g (x.1 - σ, x.2)‖ₑ)
          (hg.measurable.enorm.comp ((measurable_const.sub measurable_id).prodMk measurable_const))
    _ = (∫⁻ σ, ‖ρ σ‖ₑ) ^ (q - 1) *
          ∫⁻ x, (∫⁻ σ, ‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ ^ q) ∂cylMeasure := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right'
          (f := fun p : (ℝ × ℝ) × ℝ => ‖ρ p.2‖ₑ * ‖g (p.1.1 - p.2, p.1.2)‖ₑ ^ q)
          ((hρm.comp measurable_snd).mul (hgm.comp sca_meas_shift))
    _ = _ := by rw [sca_tonelli hρm hgm]

/-- `G ∈ L^q` for `g ∈ L^q` of the cylinder and integrable continuous `ρ`. -/
theorem sca_memLp (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : LpCyl n q) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hρi : Integrable ρ) :
    MemLp (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) q cylMeasure := by
  have hq1 : 1 ≤ q := Fact.out
  have hgs : StronglyMeasurable (g : ℝ × ℝ → Vec n) := Lp.stronglyMeasurable g
  have hGs := sca_sm hgs hρ
  have hρf : ∫⁻ σ, ‖ρ σ‖ₑ < ⊤ := hρi.2
  by_cases hqt : q = ⊤
  · subst hqt
    set M := eLpNormEssSup (g : ℝ × ℝ → Vec n) cylMeasure
    have hMt : M ≠ ⊤ := by
      have := Lp.eLpNorm_lt_top g
      rw [eLpNorm_exponent_top] at this
      exact this.ne
    set N := {y : ℝ × ℝ | M < ‖g y‖ₑ}
    have hNm : MeasurableSet N := measurableSet_lt measurable_const hgs.measurable.enorm
    have hN0 : cylMeasure N = 0 := by
      have := (ae_le_eLpNormEssSup (μ := cylMeasure) (f := (g : ℝ × ℝ → Vec n)))
      rw [ae_iff] at this
      simpa [N, not_le] using this
    have hT := sca_tonelli (k := fun _ => (1 : ℝ≥0∞)) measurable_const
      (h := N.indicator 1) (measurable_one.indicator hNm)
    rw [lintegral_indicator_one hNm, hN0, mul_zero] at hT
    have hmeasT : Measurable fun x : ℝ × ℝ => ∫⁻ σ, (fun _ => (1 : ℝ≥0∞)) σ *
        N.indicator 1 (x.1 - σ, x.2) :=
      Measurable.lintegral_prod_right'
        (f := fun p : (ℝ × ℝ) × ℝ => (fun _ => (1 : ℝ≥0∞)) p.2 * N.indicator 1 (p.1.1 - p.2, p.1.2))
        (measurable_const.mul ((measurable_one.indicator hNm).comp sca_meas_shift))
    rw [lintegral_eq_zero_iff hmeasT] at hT
    have hae : ∀ᵐ x ∂cylMeasure, ∀ᵐ σ, ‖g (x.1 - σ, x.2)‖ₑ ≤ M := by
      filter_upwards [hT] with x hx
      have hx' : ∫⁻ σ, N.indicator (1 : ℝ × ℝ → ℝ≥0∞) (x.1 - σ, x.2) = 0 := by
        simpa only [Pi.zero_apply, one_mul] using hx
      have hx'' := (lintegral_eq_zero_iff
        (f := fun σ => N.indicator (1 : ℝ × ℝ → ℝ≥0∞) (x.1 - σ, x.2)) ((measurable_one.indicator hNm).comp
        ((measurable_const.sub measurable_id).prodMk measurable_const))).1 hx'
      filter_upwards [hx''] with σ hσ
      have hσ' : N.indicator (1 : ℝ × ℝ → ℝ≥0∞) (x.1 - σ, x.2) = 0 := hσ
      by_contra hc
      have hmem : (x.1 - σ, x.2) ∈ N := lt_of_not_ge hc
      rw [Set.indicator_of_mem hmem] at hσ'
      simp at hσ'
    refine memLp_top_of_bound_enorm hGs.aestronglyMeasurable
      ((∫⁻ σ, ‖ρ σ‖ₑ) * M).toNNReal ?_
    filter_upwards [hae] with x hx
    rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top hρf.ne hMt)]
    refine (sca_enorm_le _ ρ x).trans ?_
    rw [← lintegral_mul_const _ hρ.measurable.enorm]
    exact lintegral_mono_ae (hx.mono fun σ hσ => by gcongr)
  · have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq1).ne'
    have hqr : 1 ≤ q.toReal := by
      have := ENNReal.toReal_mono hqt hq1
      simpa using this
    refine ⟨hGs.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt]
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    have hgf : ∫⁻ x, ‖g x‖ₑ ^ q.toReal ∂cylMeasure ≠ ⊤ :=
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hqt (Lp.eLpNorm_lt_top g)).ne
    refine ne_top_of_le_ne_top ?_ (sca_lintegral_le hqr hgs hρ)
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hρf.ne)
      (ENNReal.mul_ne_top hρf.ne hgf)

end

end CauchyRiemannIndex

-- ===== Scratch/CRSConvLpSol.lean =====
open MeasureTheory CauchyRiemannIndex
open scoped ENNReal

theorem solution (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : LpCyl n q) (ρ : ℝ → ℝ)
    (hρ : Continuous ρ) (hρi : Integrable ρ) :
    MemLp (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) q cylMeasure :=
  sca_memLp q g hρ hρi
