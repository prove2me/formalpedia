-- Prove2me | solution 2 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:29:20.678753+00:00
-- url     : https://prove2.me/submissions/9970914e-7733-42ee-a1e3-89cca0e46ac2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Extend local HJB verification at a positive finite barrier to all reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  let c : ℝ := (cstar W).toReal
  have hcast : ENNReal.ofReal c = cstar W :=
    ENNReal.ofReal_toReal (ne_of_lt hc)
  have hcnonneg : 0 ≤ c := ENNReal.toReal_nonneg
  obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
    vcstar_local_verification_regular_of_positive_cstar
      X hX q hq W hW hc hcpos h_smooth
  have hhjb := vcstar_hjb_below_positive_cstar
    X hX q hq W hW hc h_smooth hcpos
  obtain ⟨hinside, _⟩ := local_verification
    X hX q hq (vcstar W) (cstar W) hcpos hcont hw0 hwneg hsmooth hhjb
  intro x hx
  by_cases hxc : x ≤ c
  · apply hinside x hx
    rw [← hcast]
    exact ENNReal.ofReal_le_ofReal hxc
  · have hcx : c < x := lt_of_not_ge hxc
    have hsplit := valueFunctionLe_above_cap X q x c hcnonneg hcx
    rw [hcast] at hsplit
    have hval : valueFunctionLe X q (cstar W) c ≤
        ENNReal.ofReal (vcstar W c) :=
      hinside c hcnonneg (le_of_eq hcast)
    have hnonneg : 0 ≤ vcstar W c := by
      change 0 ≤ barrierValue W c c
      exact barrierValue_nonnegative_for_nonnegative_capital
        X hX q hq W hW c c hcnonneg hcnonneg
    have haff : vcstar W x = (x - c) + vcstar W c := by
      change barrierValue W c x = (x - c) + barrierValue W c c
      exact barrierValue_above_affine W c x hcnonneg hcx
    calc
      valueFunctionLe X q (cstar W) x =
          ENNReal.ofReal (x - c) + valueFunctionLe X q (cstar W) c := hsplit
      _ ≤ ENNReal.ofReal (x - c) + ENNReal.ofReal (vcstar W c) := by
        simpa only [add_comm] using
          (add_le_add_left hval (ENNReal.ofReal (x - c)))
      _ = ENNReal.ofReal ((x - c) + vcstar W c) :=
        (ENNReal.ofReal_add (sub_nonneg.mpr (le_of_lt hcx)) hnonneg).symm
      _ = ENNReal.ofReal (vcstar W x) := by rw [haff]
