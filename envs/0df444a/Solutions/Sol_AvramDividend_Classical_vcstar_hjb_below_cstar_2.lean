-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_hjb_below_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:27:20.416869+00:00
-- url     : https://prove2.me/submissions/75a67d54-12ee-4625-920e-b1da651fb6a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  -- HJB below c* via the two Open children from the decomposition: restrict the
  -- Ioi-smoothness to the Ioo window (all disjuncts pass through; the smooth case
  -- by ContDiffOn.mono over Ioo ⊆ Ioi), feed it with positivity of c* into the
  -- generator equation, and close the max with the derivative lower bound.
  -- Principal lemmas: generator_vcstar_eq_zero, vcstar_deriv_ge_one (both Open).
  -- Exact unresolved identities: both (smooth-fit/generator leaves).
  intro y hy0 hyc
  have hsm : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Set.Ioo 0 (cstar W).toReal) := by
    rcases h_smooth with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr
        (h.mono (fun x hx => Set.mem_Ioi.mpr (Set.mem_Ioo.mp hx).1)))
  have hmem : y ∈ Set.Ioo (0 : ℝ) (cstar W).toReal :=
    Set.mem_Ioo.mpr ⟨hy0,
      (ENNReal.ofReal_lt_iff_lt_toReal hy0.le (ne_of_lt hc)).mp hyc⟩
  have hgen := AvramDividend.Classical.generator_vcstar_eq_zero
    X hX q hq W hW hsm hcpos y hmem
  have hder := (AvramDividend.Classical.vcstar_deriv_ge_one
    X hX q hq W hW y hy0).2
  refine ⟨hgen.1, ?_⟩
  rw [hgen.2]
  exact max_eq_left (sub_nonpos.mpr hder)
