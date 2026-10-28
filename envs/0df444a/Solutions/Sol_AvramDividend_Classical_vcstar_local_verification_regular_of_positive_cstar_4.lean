-- Prove2me | solution 4 for AvramDividend.Classical.vcstar_local_verification_regular_of_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:39:58.736772+00:00
-- url     : https://prove2.me/submissions/969967cd-5616-4a61-b619-bc4e01b0c594

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C1_bv_positive_barrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaledW_contDiffOn_two_of_W_contDiffOn_two_positive
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_on_Iic_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Local verification regularity from established branchwise scale smoothness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      (∀ y < 0, vcstar W y = 0) ∧
      ((¬ X.BoundedVariation →
          ContDiffOn ℝ 2 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) ∧
       (X.BoundedVariation →
          ContDiffOn ℝ 1 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W})) := by
  let s : Set ℝ := {y | 0 < y ∧ ENNReal.ofReal y < cstar W}
  have hs : s ⊆ Ioi 0 := by
    intro y hy
    exact hy.1
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hbelow : ∀ y ∈ s, y ≤ (cstar W).toReal := by
    intro y hy
    exact le_of_lt ((ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy.1)
      (ne_of_lt hc)).mp hy.2)
  have hnbv : ¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W) s := by
    intro hno
    rcases h_smooth with hσ | hbv | hC2
    · have hW2 : ContDiffOn ℝ 2 W s :=
        (scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ).mono hs
      have hscaled : ContDiffOn ℝ 2
          (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) s :=
        scaledW_contDiffOn_two_of_W_contDiffOn_two_positive
          W (cstar W).toReal ha s hW2
      apply hscaled.congr
      intro z hz
      exact vcstar_eq_scaledW_on_Iic_cstar W hW.1 z (hbelow z hz)
    · exact False.elim (hno hbv)
    · exact hC2.mono hs
  have hbv : X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W) s := by
    intro hBV
    exact (vcstar_global_C1_bv_positive_barrier
      X hX q hq W hW hc hcpos hBV).mono hs
  obtain ⟨hcont, hzero, hneg⟩ :=
    vcstar_basic_boundary_regular_of_positive_cstar X hX q hq W hW hc hcpos
  exact ⟨hcont, hzero, hneg, ⟨hnbv, hbv⟩⟩
