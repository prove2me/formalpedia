-- Prove2me | solution 1 for DistTransform.Distortion.remark_p4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T04:02:55.682269+00:00
-- url     : https://prove2.me/submissions/e1032ac2-b903-4da3-b462-304a57bb128b

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_DTDrp4
open DistTransform.Distortion

lemma galois (F : ProbabilityMeasure ℝ) (u : ℝ) (hu0 : 0 < u)
    (hex : ∃ y, u ≤ cdf (F : Measure ℝ) y) (x : ℝ) :
    leftQuantile F u ≤ x ↔ u ≤ cdf (F : Measure ℝ) x := by
  have hne : {y : ℝ | u ≤ cdf (F : Measure ℝ) y}.Nonempty := hex
  have hbdd : BddBelow {y : ℝ | u ≤ cdf (F : Measure ℝ) y} := by
    have hev := (tendsto_cdf_atBot (μ := (F : Measure ℝ))).eventually (gt_mem_nhds hu0)
    obtain ⟨y0, hy0⟩ := hev.exists
    refine ⟨y0, fun y hy => ?_⟩
    by_contra hlt
    push Not at hlt
    have := monotone_cdf (F : Measure ℝ) hlt.le
    have hy' : u ≤ cdf (F : Measure ℝ) y := hy
    linarith
  unfold leftQuantile
  constructor
  · intro hq
    have hmem : u ≤ cdf (F : Measure ℝ) (sInf {y : ℝ | u ≤ cdf (F : Measure ℝ) y}) := by
      rw [← (cdf (F : Measure ℝ)).iInf_Ioi_eq]
      apply le_ciInf
      intro r
      obtain ⟨y, hyS, hyr⟩ := exists_lt_of_csInf_lt hne r.2
      exact hyS.trans (monotone_cdf _ hyr.le)
    exact hmem.trans (monotone_cdf _ hq)
  · intro hx
    exact csInf_le hbdd hx

lemma real_restrict_eq (S T : Set ℝ)
    (h : ∀ p ∈ Set.Ioo (0 : ℝ) 1, p ∈ S ↔ p ∈ T) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).real S = (volume.restrict (Set.Ioo (0 : ℝ) 1)).real T := by
  rw [measureReal_def, measureReal_def, Measure.restrict_apply' measurableSet_Ioo,
    Measure.restrict_apply' measurableSet_Ioo]
  congr 2
  ext p
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(h p h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(h p h2).2 h1, h2⟩

end Aux_DTDrp4

open DistTransform.Distortion Aux_DTDrp4 in
theorem solution (h : ℝ → ℝ) (hh_mono : MonotoneOn h (Set.Ioo 0 1))
    (hh_range : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1) :
    IsH0 (fun x => (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ x}) ∧
      (∀ F ∈ Minf, ∀ x : ℝ,
        (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | leftQuantile F (h p) ≤ x} =
          (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ cdf (F : Measure ℝ) x}) ∧
      ((∀ p ∈ Set.Ioo (0 : ℝ) 1, h p < 1) → ∀ (F : ProbabilityMeasure ℝ) (x : ℝ),
        (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | leftQuantile F (h p) ≤ x} =
          (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ cdf (F : Measure ℝ) x}) := by
  set μ := volume.restrict (Set.Ioo (0 : ℝ) 1) with hμ
  have hμ1 : μ Set.univ = 1 := by
    rw [hμ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo]
    simp
  haveI : IsProbabilityMeasure μ := ⟨hμ1⟩
  refine ⟨?_, ?_, ?_⟩
  · -- distortion function
    set h' : ℝ → ℝ := fun p => if p ≤ 0 then 0 else if p < 1 then h p else 1 with hh'
    have hagree : ∀ p ∈ Set.Ioo (0 : ℝ) 1, h' p = h p := by
      intro p hp
      simp only [hh', if_neg (not_le.2 hp.1), if_pos hp.2]
    have hmono' : Monotone h' := by
      intro p q hpq
      simp only [hh']
      split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> first
        | exact le_rfl
        | linarith
        | exact (hh_range q ⟨by linarith, by linarith⟩).1.le
        | exact (hh_range _ ⟨by linarith, by linarith⟩).2
        | exact hh_mono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hpq
        | (exfalso; linarith)
        | norm_num
    have hm' : Measurable h' := hmono'.measurable
    set ν := μ.map h' with hν
    haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hm'.aemeasurable
    have hG : (fun x => μ.real {p | h p ≤ x}) = ⇑(cdf ν) := by
      funext x
      rw [cdf_eq_real, hν, map_measureReal_apply hm' measurableSet_Iic]
      apply real_restrict_eq
      intro p hp
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, hagree p hp]
    rw [hG]
    refine ⟨(monotone_cdf ν).monotoneOn _, fun t _ => (cdf ν).right_continuous t, ?_, ?_⟩
    · rw [← hG]
      show μ.real {p | h p ≤ 0} = 0
      rw [real_restrict_eq {p | h p ≤ 0} ∅ (fun p hp => by
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact (hh_range p hp).1)]
      simp
    · rw [← hG]
      show μ.real {p | h p ≤ 1} = 1
      rw [real_restrict_eq {p | h p ≤ 1} Set.univ (fun p hp => by
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact (hh_range p hp).2)]
      rw [measureReal_def, hμ1]; simp
  · intro F hF x
    obtain ⟨a, b, hab⟩ := hF
    apply real_restrict_eq
    intro p hp
    simp only [Set.mem_setOf_eq]
    obtain ⟨h0, h1⟩ := hh_range p hp
    apply galois F (h p) h0 _ x
    refine ⟨b, ?_⟩
    have : cdf (F : Measure ℝ) b = 1 := by
      rw [cdf_eq_real]
      have hle : (F : Measure ℝ) (Set.Icc a b) ≤ (F : Measure ℝ) (Set.Iic b) :=
        measure_mono Set.Icc_subset_Iic_self
      rw [hab] at hle
      have : (F : Measure ℝ) (Set.Iic b) = 1 := le_antisymm prob_le_one hle
      rw [measureReal_def, this]; simp
    rw [this]; exact h1
  · intro hlt F x
    apply real_restrict_eq
    intro p hp
    simp only [Set.mem_setOf_eq]
    obtain ⟨h0, _⟩ := hh_range p hp
    apply galois F (h p) h0 _ x
    have hev := (tendsto_cdf_atTop (μ := (F : Measure ℝ))).eventually (lt_mem_nhds (hlt p hp))
    obtain ⟨y, hy⟩ := hev.exists
    exact ⟨y, hy.le⟩
