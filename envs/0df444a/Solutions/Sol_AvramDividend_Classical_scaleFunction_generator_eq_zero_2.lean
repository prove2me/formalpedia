-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_generator_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T06:22:17.855506+00:00
-- url     : https://prove2.me/submissions/2eccf2a6-7d7b-4553-83c0-bef471f20377
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_smooth
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_generatorIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
ALT0 reduction for `scaleFunction_generator_eq_zero`: the Proved
integrability lemma supplies exactly the `hint` premise of the Open
generator equation lemma; pairing them at each `x ∈ Ioo 0 a` closes
both conjuncts. Supports the c24f/e8fb/c863/88d1 harmonicity chain,
hence the stopped-renewal prerequisites of the barrier proof.
-/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by
  have hint :=
    scaleFunction_generatorIntegrable_of_smooth
      X hX q hq W hW a ha h_smooth
  have heq :=
    scaleFunction_generator_eq_q_of_generatorIntegrable
      X hX q hq W hW a ha h_smooth hint
  intro x hx
  exact ⟨hint x hx, heq x hx⟩
