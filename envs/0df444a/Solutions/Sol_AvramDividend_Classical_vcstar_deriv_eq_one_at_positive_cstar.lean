-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:48:43.579607+00:00
-- url     : https://prove2.me/submissions/a69c80eb-53fc-4139-952d-c53eafc24086
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  let c : ℝ := (cstar W).toReal
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hcne : cstar W ≠ 0 := ne_of_gt hcpos
  have hcposR : 0 < c := ENNReal.toReal_pos hcne hctop
  have hdiff : DifferentiableAt ℝ (vcstar W) c :=
    (vcstar_deriv_ge_one X hX q hq W hW c hcposR).1
  have hright : ∀ z ∈ Ici c,
      vcstar W z = (z - c) + vcstar W c := by
    intro z hz
    by_cases hzc : z = c
    · rw [hzc]
      ring
    · have hcz : c < z := lt_of_le_of_ne hz (Ne.symm hzc)
      have hcz_val :=
        barrierValue_above_affine W c z (le_of_lt hcposR) hcz
      simpa [vcstar, c] using hcz_val
  have hlin :
      HasDerivAt (fun z : ℝ => z - c + vcstar W c) 1 c :=
    ((hasDerivAt_id c).sub_const c).add_const _
  have hwithin : HasDerivWithinAt (vcstar W) 1 (Ici c) c :=
    hlin.hasDerivWithinAt.congr hright
      (hright c (by simp))
  have hder := (uniqueDiffWithinAt_Ici c).eq_deriv (Ici c)
    hdiff.hasDerivAt.hasDerivWithinAt hwithin
  simpa [c] using hder
