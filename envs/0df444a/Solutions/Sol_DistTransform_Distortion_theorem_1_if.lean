-- Prove2me | solution 1 for DistTransform.Distortion.theorem_1_if
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:38:46.421973+00:00
-- url     : https://prove2.me/submissions/0cb89115-d9db-49af-ba83-8f9989a5c7f2

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_DTDif
open DistTransform.Distortion

lemma ioi_eq (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    (μ : Measure ℝ) {ω | x < id ω} = ENNReal.ofReal (1 - cdf (μ : Measure ℝ) x) := by
  have h1 : {ω : ℝ | x < id ω} = (Set.Iic x)ᶜ := by ext; simp
  rw [h1, prob_compl_eq_one_sub measurableSet_Iic, cdf_eq_real, measureReal_def,
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal
      (measure_ne_top _ _)]

lemma stLE_iff (F G : ProbabilityMeasure ℝ) :
    StLE F G ↔ ∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x := by
  unfold StLE StochasticOrders.Usual.UsualOrder
  refine forall_congr' fun x => ?_
  rw [ioi_eq, ioi_eq, ENNReal.ofReal_le_ofReal_iff]
  · constructor <;> intro h <;> linarith
  · linarith [cdf_le_one (G : Measure ℝ) x]

lemma cdf_shape (φ : ℝ ≃o ℝ) (F : ProbabilityMeasure ℝ) (x : ℝ) :
    cdf (shape φ F : Measure ℝ) x = cdf (F : Measure ℝ) (φ.symm x) := by
  rw [cdf_eq_real, cdf_eq_real, shape, ProbabilityMeasure.toMeasure_map,
    measureReal_def, measureReal_def, Measure.map_apply φ.continuous.measurable measurableSet_Iic,
    OrderIso.preimage_Iic]

lemma pm_ext (μ ν : ProbabilityMeasure ℝ)
    (h : ∀ x, cdf (μ : Measure ℝ) x = cdf (ν : Measure ℝ) x) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.eq_of_cdf _ _ (StieltjesFunction.ext h)

lemma shape_mapsTo (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = Minf)
    (φ : ℝ ≃o ℝ) : Set.MapsTo (shape φ) M M := by
  rcases hM with rfl | rfl
  · exact Set.mapsTo_univ _ _
  · rintro F ⟨a, b, hab⟩
    refine ⟨φ a, φ b, ?_⟩
    rw [shape, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply φ.continuous.measurable measurableSet_Icc, OrderIso.preimage_Icc]
    simpa using hab

end Aux_DTDif

open Aux_DTDif in
theorem solution (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = DistTransform.Distortion.Minf)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (hT : Set.MapsTo T M M)
    (hT_dist : DistTransform.Distortion.IsProbabilityDistortion M T) :
    DistTransform.Distortion.IsLSC M T ∧ DistTransform.Distortion.IsMonotoneT M T ∧
      DistTransform.Distortion.CommutesWithShape M T := by
  open DistTransform.Distortion in
  obtain ⟨g, ⟨hgmono, hgrc, hg0, hg1⟩, hTg⟩ := hT_dist
  have cdf_mem : ∀ (μ : ProbabilityMeasure ℝ) x, cdf (μ : Measure ℝ) x ∈ Set.Icc (0:ℝ) 1 :=
    fun μ x => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  refine ⟨?_, ?_, ?_⟩
  · -- lower semicontinuity
    intro Fs F G hFs hF hG hlim hle
    rw [stLE_iff]
    intro x
    have hle' : ∀ n, cdf (G : Measure ℝ) x ≤ g (cdf (Fs n : Measure ℝ) x) := by
      intro n
      have := (stLE_iff _ _).1 (hle n) x
      rwa [hTg _ (hFs n)] at this
    rw [hTg _ hF]
    obtain ⟨c, hc⟩ : ∃ c, c = cdf (F : Measure ℝ) x := ⟨_, rfl⟩
    rw [← hc]
    have hcmem : c ∈ Set.Icc (0:ℝ) 1 := hc ▸ cdf_mem F x
    rcases eq_or_lt_of_le hcmem.2 with h1 | h1
    · rw [h1, hg1]; exact cdf_le_one _ _
    by_contra hcon
    push Not at hcon
    have hrc := hgrc c ⟨hcmem.1, h1⟩
    have ev1 : ∀ᶠ t in 𝓝[>] c, g t < cdf (G : Measure ℝ) x :=
      nhdsWithin_mono _ Set.Ioi_subset_Ici_self (hrc.eventually (gt_mem_nhds hcon))
    have ev2 : ∀ᶠ t in 𝓝[>] c, t < 1 :=
      nhdsWithin_le_nhds (gt_mem_nhds h1)
    have ev3 : ∀ᶠ t in 𝓝[>] c, t ∈ Set.Ioi c := eventually_mem_nhdsWithin
    obtain ⟨t, ⟨ht1, htg⟩, htc⟩ := ((ev2.and ev1).and ev3).exists
    have hls := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim
      (isClosed_Iic (a := x))
    have hlt : (F : Measure ℝ) (Set.Iic x) < ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top (F : Measure ℝ) (Set.Iic x))]
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith [hcmem.1, Set.mem_Ioi.1 htc])]
      rw [hc, cdf_eq_real, measureReal_def] at htc
      exact htc
    have hev := eventually_lt_of_limsup_lt (lt_of_le_of_lt hls hlt)
    obtain ⟨n, hn⟩ := hev.exists
    have hn' : cdf (Fs n : Measure ℝ) x < t := by
      rw [cdf_eq_real, measureReal_def]
      exact ENNReal.toReal_lt_of_lt_ofReal hn
    have := hgmono (cdf_mem _ x) ⟨by linarith [hcmem.1, Set.mem_Ioi.1 htc], ht1.le⟩ hn'.le
    linarith [hle' n]
  · -- monotonicity
    intro F hF G hG hFG
    rw [stLE_iff] at hFG ⊢
    intro x
    rw [hTg _ hF, hTg _ hG]
    exact hgmono (cdf_mem _ x) (cdf_mem _ x) (hFG x)
  · -- commutation with shape transforms
    intro φ
    refine ⟨shape_mapsTo M hM φ, fun F hF => ?_⟩
    apply pm_ext
    intro x
    rw [hTg _ (shape_mapsTo M hM φ hF), cdf_shape, cdf_shape, hTg _ hF]
