-- Prove2me | solution 1 for DistTransform.Distortion.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:40:01.742993+00:00
-- url     : https://prove2.me/submissions/fe50efce-ba32-4d5e-8180-a7ac7965cc99

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model
import Theorems.Thm_DistTransform_Distortion_theorem_1_if
import Theorems.Thm_DistTransform_Distortion_eq_4
import Theorems.Thm_DistTransform_Distortion_m0_conclusion
import Theorems.Thm_DistTransform_Distortion_remark_p4

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_DTDthm1
open DistTransform.Distortion

/-- Lebesgue measure on `(0,1)` of `{p ≤ c}` is `c` for `c ∈ [0,1]`. -/
lemma unif_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | p ≤ c} = c := by
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Ioo]
  have h1 : volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) = ENNReal.ofReal c := by
    apply le_antisymm
    · calc volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) ≤ volume (Set.Ioc (0:ℝ) c) := by
            apply measure_mono
            rintro p ⟨hp, hp0, _⟩
            exact ⟨hp0, hp⟩
        _ = ENNReal.ofReal c := by rw [Real.volume_Ioc]; simp
    · calc ENNReal.ofReal c = volume (Set.Ioo (0:ℝ) c) := by rw [Real.volume_Ioo]; simp
        _ ≤ volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) := by
            apply measure_mono
            rintro p ⟨hp0, hp⟩
            exact ⟨le_of_lt hp, hp0, lt_of_lt_of_le hp hc1⟩
  rw [h1, ENNReal.toReal_ofReal hc0]

/-- The cdf of any distribution is recovered from its left quantile function under the
uniform distribution on `(0,1)` (remark on p. 4 with `h = id`). -/
lemma cdf_eq_unif_quantile (G : ProbabilityMeasure ℝ) (x : ℝ) :
    cdf (G : Measure ℝ) x =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | leftQuantile G p ≤ x} := by
  have hr := (remark_p4 id (monotoneOn_id) (fun p hp => ⟨hp.1, hp.2.le⟩)).2.2
    (fun p hp => hp.2) G x
  simp only [id] at hr
  rw [hr, unif_le _ (cdf_nonneg _ _) (cdf_le_one _ _)]

lemma restrict_congr_Ioo (S S' : Set ℝ) (h : ∀ p ∈ Set.Ioo (0:ℝ) 1, (p ∈ S ↔ p ∈ S')) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).real S =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).real S' := by
  rw [measureReal_def, measureReal_def, Measure.restrict_apply' measurableSet_Ioo,
    Measure.restrict_apply' measurableSet_Ioo]
  congr 2
  ext p
  constructor
  · rintro ⟨hp, hp'⟩; exact ⟨(h p hp').1 hp, hp'⟩
  · rintro ⟨hp, hp'⟩; exact ⟨(h p hp').2 hp, hp'⟩

end Aux_DTDthm1

open DistTransform.Distortion Aux_DTDthm1 in
theorem solution (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = Minf)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (hT : Set.MapsTo T M M) :
    (IsLSC M T ∧ IsMonotoneT M T ∧ CommutesWithShape M T) ↔ IsProbabilityDistortion M T := by
  constructor
  · rintro ⟨hl, hm, hc⟩
    -- Step 1: a quantile-level function `h` with `q_p(T F) = F⁻¹(h p)` on `M`
    -- (eq. (4) on `M∞`, and its extension to `M0` with `h < 1`), plus the cdf identity
    -- of the remark on p. 4 for that `h`.
    obtain ⟨h, hmono, hrange, hq, hcdf⟩ : ∃ h : ℝ → ℝ, MonotoneOn h (Set.Ioo 0 1) ∧
        (∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1) ∧
        (∀ F ∈ M, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p)) ∧
        (∀ F ∈ M, ∀ x : ℝ,
          (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | leftQuantile F (h p) ≤ x} =
            (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ cdf (F : Measure ℝ) x}) := by
      rcases hM with rfl | rfl
      · obtain ⟨h, hmono, hrange, hq⟩ := m0_conclusion T hl hm hc
        have hrange' : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1 :=
          fun p hp => ⟨(hrange p hp).1, (hrange p hp).2.le⟩
        refine ⟨h, hmono, hrange', fun F _ => hq F, fun F _ x => ?_⟩
        exact (remark_p4 h hmono hrange').2.2 (fun p hp => (hrange p hp).2) F x
      · obtain ⟨h, hmono, hrange, hq⟩ := eq_4 Minf (Or.inr rfl) T hT hl hm hc
        exact ⟨h, hmono, hrange, hq, (remark_p4 h hmono hrange).2.1⟩
    -- Step 2: `g(y) = P(h(U) ≤ y)` is the distortion function.
    refine ⟨fun y => (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ y},
      (remark_p4 h hmono hrange).1, fun F hF x => ?_⟩
    rw [cdf_eq_unif_quantile]
    show _ = (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | h p ≤ cdf (F : Measure ℝ) x}
    rw [← hcdf F hF x]
    apply restrict_congr_Ioo
    intro p hp
    simp only [Set.mem_setOf_eq, hq F hF p hp]
  · intro hd
    exact theorem_1_if M hM T hT hd
