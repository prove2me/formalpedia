-- Prove2me | solution 1 for BHTOpinion.Continuum.lemma1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:42:16.896202+00:00
-- url     : https://prove2.me/submissions/7caa5007-3a6e-4cc1-8d4d-91c7c674f014

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHT6L1

open BHTOpinion.Continuum

/-- The integrand of `opL` is integrable on `I` whenever `x` is a.e.-measurable on `I`. -/
lemma integrand_integrable (x : ℝ → ℝ) (hx : AEMeasurable x (volume.restrict I)) (α : ℝ) :
    Integrable (fun γ => if |x α - x γ| < 1 then x γ - x α else 0) (volume.restrict I) := by
  have : IsFiniteMeasure (volume.restrict I) := by
    rw [isFiniteMeasure_restrict]; exact measure_Icc_lt_top.ne
  refine Integrable.of_bound (C := 1) ?_ ?_
  · have hm : AEMeasurable (fun γ => if |x α - x γ| < 1 then x γ - x α else 0)
        (volume.restrict I) := by
      refine ⟨fun γ => if |x α - hx.mk x γ| < 1 then hx.mk x γ - x α else 0, ?_, ?_⟩
      · refine Measurable.ite ?_ (hx.measurable_mk.sub measurable_const) measurable_const
        exact measurableSet_lt ((measurable_const.sub hx.measurable_mk).abs) measurable_const
      · filter_upwards [hx.ae_eq_mk] with γ hγ
        simp only [hγ]
    exact hm.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun γ => ?_)
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_sub_comm]; exact h.le
    · simp

lemma aem_of_Y (x : ℝ → ℝ) (hx : InY x) : AEMeasurable x (volume.restrict I) :=
  aemeasurable_restrict_of_measurable_subtype measurableSet_Icc hx.1

lemma vol_I_real : (volume.restrict I).real Set.univ = 1 := by
  simp [measureReal_def, Real.volume_Icc]

/-- Key measure bound: for `x ∈ X_m`, the agents in `I` whose opinion lies in an interval of
length `w` are contained in an interval of length `w / m`. -/
lemma preimage_small (m : ℝ) (hm : 0 < m) (x : ℝ → ℝ) (hx : InXm m x) (p w : ℝ) (hw : 0 ≤ w) :
    ∃ J : Set ℝ, MeasurableSet J ∧ volume J ≠ ⊤ ∧ volume.real J ≤ w / m ∧
      ∀ γ ∈ I, p ≤ x γ → x γ ≤ p + w → γ ∈ J := by
  classical
  set T : Set ℝ := {γ | γ ∈ I ∧ p ≤ x γ ∧ x γ ≤ p + w} with hT
  by_cases hne : T.Nonempty
  · have hbdd : BddBelow T := ⟨0, fun γ hγ => hγ.1.1⟩
    set c := sInf T
    refine ⟨Set.Icc c (c + w / m), measurableSet_Icc, measure_Icc_lt_top.ne, ?_, ?_⟩
    · rw [Real.volume_real_Icc]
      have : 0 ≤ w / m := div_nonneg hw hm.le
      rw [max_eq_left (by linarith)]; linarith
    · intro γ hγ h1 h2
      have hγT : γ ∈ T := ⟨hγ, h1, h2⟩
      refine ⟨csInf_le hbdd hγT, ?_⟩
      by_contra hcon
      push Not at hcon
      have hlt : sInf T < γ - w / m := by linarith
      obtain ⟨t', ht'T, ht'lt⟩ := exists_lt_of_csInf_lt hne hlt
      have hlt' : t' < γ := by
        have : 0 ≤ w / m := div_nonneg hw hm.le
        linarith
      have key := hx.2 t' ht'T.1 γ hγ hlt'
      have : x γ - x t' ≤ w := by linarith [ht'T.2.1]
      have h3 : m * (γ - t') ≤ w := le_trans key this
      have h4 : γ - t' ≤ w / m := by
        rw [le_div_iff₀ hm]; linarith
      linarith
  · refine ⟨∅, MeasurableSet.empty, by simp, ?_, ?_⟩
    · simp; exact div_nonneg hw hm.le
    · intro γ hγ h1 h2
      exact absurd ⟨γ, hγ, h1, h2⟩ hne

end BHT6L1

open BHTOpinion.Continuum in
theorem solution (m : ℝ) (hm : 0 < m) (x y : ℝ → ℝ)
    (hx : InXm m x) (hy : InY y) (δ : ℝ) (hδ : ∀ γ ∈ I, |x γ - y γ| ≤ δ) :
    ∀ α ∈ I, |opL x α - opL y α| ≤ (2 + 8 / m) * δ := by
  intro α hα
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ α hα)
  have haex : AEMeasurable x (volume.restrict I) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Icc hx.1.1
  have haey := BHT6L1.aem_of_Y y hy
  have ix := BHT6L1.integrand_integrable x haex α
  have iy := BHT6L1.integrand_integrable y haey α
  have hfin : IsFiniteMeasure (volume.restrict I) := by
    rw [isFiniteMeasure_restrict]; exact measure_Icc_lt_top.ne
  obtain ⟨J1, hJ1m, hJ1f, hJ1v, hJ1⟩ :=
    BHT6L1.preimage_small m hm x hx (x α + 1 - 2 * δ) (4 * δ) (by linarith)
  obtain ⟨J2, hJ2m, hJ2f, hJ2v, hJ2⟩ :=
    BHT6L1.preimage_small m hm x hx (x α - 1 - 2 * δ) (4 * δ) (by linarith)
  have hint1 : Integrable (J1.indicator (1 : ℝ → ℝ)) (volume.restrict I) :=
    (integrable_const (1 : ℝ)).indicator hJ1m
  have hint2 : Integrable (J2.indicator (1 : ℝ → ℝ)) (volume.restrict I) :=
    (integrable_const (1 : ℝ)).indicator hJ2m
  have hdiff : opL x α - opL y α = ∫ γ in I,
      ((if |x α - x γ| < 1 then x γ - x α else 0) -
        (if |y α - y γ| < 1 then y γ - y α else 0)) := by
    unfold opL; rw [integral_sub ix iy]
  have hδα := hδ α hα
  rw [abs_le] at hδα
  rw [hdiff, ← Real.norm_eq_abs]
  calc ‖∫ γ in I, ((if |x α - x γ| < 1 then x γ - x α else 0) -
        (if |y α - y γ| < 1 then y γ - y α else 0))‖
      ≤ ∫ γ in I, (2 * δ + (J1.indicator (1 : ℝ → ℝ) γ + J2.indicator (1 : ℝ → ℝ) γ)) := by
        refine norm_integral_le_of_norm_le ((integrable_const _).add (hint1.add hint2)) ?_
        rw [ae_restrict_iff' measurableSet_Icc]
        refine Filter.Eventually.of_forall (fun γ hγ => ?_)
        have i1 : 0 ≤ J1.indicator (1 : ℝ → ℝ) γ :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) γ
        have i2 : 0 ≤ J2.indicator (1 : ℝ → ℝ) γ :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) γ
        have hδγ := hδ γ hγ
        rw [abs_le] at hδγ
        rw [Real.norm_eq_abs]
        split_ifs with h1 h2 h2
        · rw [abs_le]; constructor <;> linarith
        · -- x-connected, not y-connected
          rw [abs_lt] at h1; rw [not_lt, le_abs] at h2
          rcases h2 with h2 | h2
          · -- y α - y γ ≥ 1 : x γ near x α - 1
            have hmem := hJ2 γ hγ (by linarith) (by linarith)
            rw [Set.indicator_of_mem hmem, sub_zero]
            simp only [Pi.one_apply]
            have : |x γ - x α| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
            linarith
          · have hmem := hJ1 γ hγ (by linarith) (by linarith)
            rw [Set.indicator_of_mem hmem, sub_zero]
            simp only [Pi.one_apply]
            have : |x γ - x α| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
            linarith
        · -- y-connected, not x-connected
          rw [abs_lt] at h2; rw [not_lt, le_abs] at h1
          rcases h1 with h1 | h1
          · have hmem := hJ2 γ hγ (by linarith) (by linarith)
            rw [Set.indicator_of_mem hmem, zero_sub, abs_neg]
            simp only [Pi.one_apply]
            have : |y γ - y α| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
            linarith
          · have hmem := hJ1 γ hγ (by linarith) (by linarith)
            rw [Set.indicator_of_mem hmem, zero_sub, abs_neg]
            simp only [Pi.one_apply]
            have : |y γ - y α| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
            linarith
        · simp; linarith
    _ = 2 * δ + ((volume.restrict I).real J1 + (volume.restrict I).real J2) := by
        have h := integral_add (integrable_const (2 * δ)) (hint1.add hint2)
        have h' := integral_add hint1 hint2
        simp only [Pi.add_apply] at h h'
        rw [h, h', integral_indicator_one hJ1m, integral_indicator_one hJ2m, integral_const]
        simp [measureReal_def, Real.volume_Icc]
    _ ≤ 2 * δ + (volume.real J1 + volume.real J2) := by
        gcongr
        · rw [measureReal_restrict_apply hJ1m]; exact measureReal_mono Set.inter_subset_left hJ1f
        · rw [measureReal_restrict_apply hJ2m]; exact measureReal_mono Set.inter_subset_left hJ2f
    _ ≤ 2 * δ + (4 * δ / m + 4 * δ / m) := by gcongr
    _ = (2 + 8 / m) * δ := by ring
