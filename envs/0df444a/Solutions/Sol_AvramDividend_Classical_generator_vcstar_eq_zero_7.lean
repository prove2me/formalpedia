-- Prove2me | solution 7 for AvramDividend.Classical.generator_vcstar_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:14:05.154327+00:00
-- url     : https://prove2.me/submissions/f8b2b8f5-a3fc-4fcf-b5ad-e4f795e38627
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

-- Lemma 4 transfer: below cstar the barrier candidate coincides with the
-- scaled scale function, so its q-harmonicity lifts through the local
-- generator agreement lemma. Uses one Open analytic premise (c863).
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x = 0 := by
  intro x hxmem
  have hxbelow : x < (cstar W).toReal := hxmem.2
  have hagreeBelow :
      ∀ z : ℝ, z < (cstar W).toReal →
        vcstar W z =
          divE (W z) (scaleDeriv W (cstar W).toReal) := by
    intro z hzbelow
    show barrierValue W (cstar W).toReal z =
      divE (W z) (scaleDeriv W (cstar W).toReal)
    by_cases hneg : z < 0
    · simp [barrierValue, hneg, hW.1 z hneg, divE]
    · have hzle : z ≤ (cstar W).toReal := le_of_lt hzbelow
      simp [barrierValue, hneg, hzle]
  have hscaled :=
    scaled_scaleFunction_q_harmonic_below_cstar
      X hX q hq W hW h_smooth hc x hxmem
  have hloc :=
    generator_eq_of_agree_below X (vcstar W)
      (fun z => divE (W z) (scaleDeriv W (cstar W).toReal))
      (cstar W).toReal x hxbelow hagreeBelow
  refine ⟨hloc.1.mpr hscaled.1, ?_⟩
  have hval : vcstar W x = divE (W x) (scaleDeriv W (cstar W).toReal) :=
    hagreeBelow x hxbelow
  rw [hloc.2, hval]
  exact hscaled.2
