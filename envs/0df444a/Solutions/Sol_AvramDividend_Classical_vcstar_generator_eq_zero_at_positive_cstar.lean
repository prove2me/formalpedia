-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_generator_eq_zero_at_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:32:21.510696+00:00
-- url     : https://prove2.me/submissions/bd21f764-1d48-41fc-9eb2-f404930a92e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_eq_at_barrier_of_weighted_jet
import Theorems.Thm_AvramDividend_Classical_scaledW_generator_harmonic_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_scaledW_matched_weighted_jet_at_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  let a : ℝ := (cstar W).toReal
  let U : ℝ → ℝ :=
    fun z => divE (W z) (scaleDeriv W a)
  have hharm :=
    scaledW_generator_harmonic_at_positive_cstar
      X hX q hq W hW hc hcpos h_smooth
  obtain ⟨hvalues, hder, hweighted⟩ :=
    vcstar_scaledW_matched_weighted_jet_at_cstar
      X hX q hq W hW hc hcpos h_smooth
  have hgen_eq :=
    generator_eq_at_barrier_of_weighted_jet
      X (vcstar W) U a hvalues hder hweighted
  refine ⟨hgen_eq.1.mpr hharm.1, ?_⟩
  have hvalue : vcstar W a = U a := hvalues a (le_refl _)
  calc
    X.generator (vcstar W) a - q * vcstar W a =
      X.generator U a - q * U a := by rw [hgen_eq.2, hvalue]
    _ = 0 := hharm.2
