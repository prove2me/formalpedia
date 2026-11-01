-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_vcstar_global_continuous_of_zero_scale_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:42:56.766126+00:00
-- url     : https://prove2.me/submissions/a2c65b99-280d-4f26-8b30-02190ea9372c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_on_Iic_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A positive-barrier candidate is continuous on the entire line when its scale function vanishes at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hzero : W 0 = 0) :
    Continuous (vcstar W) := by
  obtain ⟨hright, _, hneg⟩ :=
    vcstar_basic_boundary_regular_of_positive_cstar X hX q hq W hW hc hcpos
  have hvzero : vcstar W 0 = 0 := by
    calc
      vcstar W 0 =
          divE (W 0) (scaleDeriv W (cstar W).toReal) :=
        vcstar_eq_scaledW_on_Iic_cstar W hW.1 0 ENNReal.toReal_nonneg
      _ = 0 := by simp [hzero, divE]
  have hleft : ContinuousOn (vcstar W) (Iic (0 : ℝ)) := by
    have heq : Set.EqOn (vcstar W) (fun _ : ℝ => 0) (Iic 0) := by
      intro z hz
      by_cases hzneg : z < 0
      · exact hneg z hzneg
      · have hz0 : z = 0 := le_antisymm hz (le_of_not_gt hzneg)
        simpa [hz0, hvzero]
    exact continuousOn_const.congr heq
  have hunion :
      ContinuousOn (vcstar W) (Iic (0 : ℝ) ∪ Ici 0) :=
    hleft.union_of_isClosed hright isClosed_Iic isClosed_Ici
  have hfull : Iic (0 : ℝ) ∪ Ici 0 = Set.univ := by
    ext z
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total z 0
  simpa [hfull] using hunion
