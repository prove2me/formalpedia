-- Prove2me | solution 1 for DistTransform.Distortion.claims_i_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:41:27.454486+00:00
-- url     : https://prove2.me/submissions/2cf990f4-6428-4658-867b-182d50b3b397

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_DTDcl
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

lemma qset_nonempty (F : ProbabilityMeasure ℝ) {p : ℝ} (hp1 : p < 1) :
    {x : ℝ | p ≤ cdf (F : Measure ℝ) x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (μ := (F : Measure ℝ))).eventually
    (lt_mem_nhds hp1)).exists
  exact ⟨x, hx.le⟩

lemma qset_bdd (F : ProbabilityMeasure ℝ) {p : ℝ} (hp0 : 0 < p) :
    BddBelow {x : ℝ | p ≤ cdf (F : Measure ℝ) x} := by
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 ((tendsto_cdf_atBot (μ := (F : Measure ℝ))).eventually
    (gt_mem_nhds hp0))
  refine ⟨a, fun x hx => ?_⟩
  by_contra hxa
  push Not at hxa
  have := ha x hxa.le
  simp only [Set.mem_setOf_eq] at hx
  linarith

lemma leftQuantile_shape (φ : ℝ ≃o ℝ) (F : ProbabilityMeasure ℝ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : leftQuantile (shape φ F) p = φ (leftQuantile F p) := by
  unfold leftQuantile
  rw [OrderIso.map_csInf' φ (qset_nonempty F hp1) (qset_bdd F hp0)]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, cdf_shape]
  constructor
  · intro hy; exact ⟨φ.symm y, hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩; simpa using hx

lemma leftQuantile_mono {F G : ProbabilityMeasure ℝ}
    (h : ∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : leftQuantile F p ≤ leftQuantile G p := by
  unfold leftQuantile
  exact csInf_le_csInf (qset_bdd F hp0) (qset_nonempty G hp1)
    (fun x hx => le_trans hx (h x))

end Aux_DTDcl

open DistTransform.Distortion Aux_DTDcl in
theorem solution (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = Minf)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (hT : Set.MapsTo T M M)
    (hmono : IsMonotoneT M T) (hcomm : CommutesWithShape M T)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ F ∈ M, ∀ G ∈ M, StLE F G → leftQuantile (T F) p ≤ leftQuantile (T G) p) ∧
      (∀ φ : ℝ ≃o ℝ, ∀ F ∈ M, leftQuantile (T (shape φ F)) p = φ (leftQuantile (T F) p)) := by
  refine ⟨fun F hF G hG hFG => ?_, fun φ F hF => ?_⟩
  · exact leftQuantile_mono ((stLE_iff _ _).1 (hmono F hF G hG hFG)) hp0 hp1
  · rw [(hcomm φ).2 F hF, leftQuantile_shape φ (T F) hp0 hp1]
