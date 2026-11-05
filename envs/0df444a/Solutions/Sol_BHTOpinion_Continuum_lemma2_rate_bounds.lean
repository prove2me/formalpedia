-- Prove2me | solution 1 for BHTOpinion.Continuum.lemma2_rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:41:13.004969+00:00
-- url     : https://prove2.me/submissions/dd1d1049-c604-431d-ba29-b4407b6f3359

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHT6L2

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

end BHT6L2

open BHTOpinion.Continuum in
theorem solution (x : ℝ → ℝ) (hx : InY x) (α β : ℝ)
    (hα : α ∈ I) (hβ : β ∈ I) (hle : x α ≤ x β) :
    -(x β - x α) ≤ opL x β - opL x α ∧
      ∀ m : ℝ, 0 < m → InXm m x → opL x β - opL x α ≤ 2 / m * (x β - x α) := by
  have haem := BHT6L2.aem_of_Y x hx
  have iα := BHT6L2.integrand_integrable x haem α
  have iβ := BHT6L2.integrand_integrable x haem β
  have hdiff : opL x β - opL x α = ∫ γ in I,
      ((if |x β - x γ| < 1 then x γ - x β else 0) -
        (if |x α - x γ| < 1 then x γ - x α else 0)) := by
    unfold opL; rw [integral_sub iβ iα]
  have : IsFiniteMeasure (volume.restrict I) := by
    rw [isFiniteMeasure_restrict]; exact measure_Icc_lt_top.ne
  refine ⟨?_, ?_⟩
  · rw [hdiff]
    have : ∫ _γ in I, (-(x β - x α)) ≤ ∫ γ in I,
        ((if |x β - x γ| < 1 then x γ - x β else 0) -
          (if |x α - x γ| < 1 then x γ - x α else 0)) := by
      refine integral_mono (integrable_const _) (iβ.sub iα) (fun γ => ?_)
      simp only
      split_ifs with h1 h2 h2
      · linarith
      · -- β connected, α not
        rw [abs_lt] at h1; rw [not_lt, le_abs] at h2
        rcases h2 with h2 | h2 <;> linarith
      · rw [not_lt] at h1; rw [abs_lt] at h2; rw [le_abs] at h1
        rcases h1 with h1 | h1 <;> linarith
      · linarith
    rw [integral_const] at this
    simpa [measureReal_def, Real.volume_Icc] using this
  · intro m hm hxm
    set d := x β - x α with hd
    have hd0 : 0 ≤ d := by linarith
    obtain ⟨J1, hJ1m, hJ1f, hJ1v, hJ1⟩ := BHT6L2.preimage_small m hm x hxm (x α + 1) d hd0
    obtain ⟨J2, hJ2m, hJ2f, hJ2v, hJ2⟩ := BHT6L2.preimage_small m hm x hxm (x α - 1) d hd0
    have hint1 : Integrable (J1.indicator (1 : ℝ → ℝ)) (volume.restrict I) :=
      (integrable_const (1 : ℝ)).indicator hJ1m
    have hint2 : Integrable (J2.indicator (1 : ℝ → ℝ)) (volume.restrict I) :=
      (integrable_const (1 : ℝ)).indicator hJ2m
    rw [hdiff]
    calc ∫ γ in I, ((if |x β - x γ| < 1 then x γ - x β else 0) -
          (if |x α - x γ| < 1 then x γ - x α else 0))
        ≤ ∫ γ in I, (J1.indicator (1 : ℝ → ℝ) γ + J2.indicator (1 : ℝ → ℝ) γ) := by
          refine setIntegral_mono_on (iβ.sub iα) (hint1.add hint2) measurableSet_Icc
            (fun γ hγ => ?_)
          have i1 : 0 ≤ J1.indicator (1 : ℝ → ℝ) γ :=
            Set.indicator_nonneg (fun _ _ => zero_le_one) γ
          have i2 : 0 ≤ J2.indicator (1 : ℝ → ℝ) γ :=
            Set.indicator_nonneg (fun _ _ => zero_le_one) γ
          split_ifs with h1 h2 h2
          · linarith
          · rw [abs_lt] at h1; rw [not_lt, le_abs] at h2
            have hu : x α + 1 ≤ x γ := by rcases h2 with h2 | h2 <;> linarith
            have hmem := hJ1 γ hγ hu (by linarith)
            rw [Set.indicator_of_mem hmem]; simp; linarith
          · rw [not_lt] at h1; rw [abs_lt] at h2; rw [le_abs] at h1
            have hu : x γ ≤ x β - 1 := by rcases h1 with h1 | h1 <;> linarith
            have hmem := hJ2 γ hγ (by linarith) (by linarith)
            rw [Set.indicator_of_mem hmem]; simp; linarith
          · linarith
      _ = (volume.restrict I).real J1 + (volume.restrict I).real J2 := by
          rw [integral_add hint1 hint2, integral_indicator_one hJ1m,
            integral_indicator_one hJ2m]
      _ ≤ volume.real J1 + volume.real J2 := by
          gcongr
          · rw [measureReal_restrict_apply hJ1m]; exact measureReal_mono Set.inter_subset_left hJ1f
          · rw [measureReal_restrict_apply hJ2m]; exact measureReal_mono Set.inter_subset_left hJ2f
      _ ≤ d / m + d / m := add_le_add hJ1v hJ2v
      _ = 2 / m * d := by ring
