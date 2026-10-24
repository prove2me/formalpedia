-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_basic_boundary_regular_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:50:13.006698+00:00
-- url     : https://prove2.me/submissions/861a5223-dced-480e-8029-3bfc2df363d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_barrierValue_positive_barrier_boundary_regular

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The positive-cstar boundary package follows from the open global
scale-derivative positivity theorem and proved deterministic barrier gluing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      ∀ y < 0, vcstar W y = 0 := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hcont : ContinuousOn W (Ici (0 : ℝ)) := hW.2.2.1
  have hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x := hW.2.1
  have hdpos : 0 < deriv W (cstar W).toReal :=
    scaleDeriv_pos X hX q hq W hW _ ha
  simpa [vcstar] using
    (barrierValue_positive_barrier_boundary_regular
      W (cstar W).toReal ha hcont hnonneg hdpos)
