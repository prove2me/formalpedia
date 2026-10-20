-- Prove2me | solution 2 for AvramDividend.Classical.generator_vcstar_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:41:43.172929+00:00
-- url     : https://prove2.me/submissions/3cc80cbd-8d45-4daa-ad85-1fc4bb8966de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_eq_of_agree_below
import Theorems.Thm_AvramDividend_Classical_scaled_scaleFunction_q_harmonic_below_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x = 0 := by
  let a : ℝ := (cstar W).toReal
  let g : ℝ → ℝ := fun z => divE (W z) (scaleDeriv W ((cstar W).toReal))
  intro x hx
  have hx_lt : x < a := (Set.mem_Ioo.mp hx).2
  have hharm :=
    scaled_scaleFunction_q_harmonic_below_cstar X hX q hq W hW h_smooth hc x hx
  have hagree : ∀ z : ℝ, z < a → vcstar W z = g z := by
    intro z hz
    by_cases hz0 : z < 0
    · have hWz : W z = 0 := hW.1 z hz0
      simp [vcstar, barrierValue, g, hz0, hWz, divE]
    · have hzn : 0 ≤ z := le_of_not_gt hz0
      have hza : z ≤ (cstar W).toReal := by
        simpa [a] using le_of_lt hz
      simp [vcstar, barrierValue, g, not_lt_of_ge hzn, hza]
  have hlocal := generator_eq_of_agree_below X (vcstar W) g a x hx_lt hagree
  refine ⟨hlocal.1.mpr hharm.1, ?_⟩
  rw [hlocal.2, hagree x hx_lt]
  exact hharm.2
