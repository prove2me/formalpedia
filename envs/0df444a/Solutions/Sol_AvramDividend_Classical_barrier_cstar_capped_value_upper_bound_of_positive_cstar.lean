-- Prove2me | solution 1 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:26:21.905861+00:00
-- url     : https://prove2.me/submissions/d08d1aee-ba2f-4613-a7b3-5f21121ae824
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap

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
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  let c : ℝ := (cstar W).toReal
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hcne : cstar W ≠ 0 := ne_of_gt hcpos
  have hcposR : 0 < c := by
    exact ENNReal.toReal_pos hcne hctop
  have hcap : ENNReal.ofReal c = cstar W := by
    simpa [c] using ENNReal.ofReal_toReal hctop

  rcases
      vcstar_local_verification_regular_of_positive_cstar
        X hX q hq W hW hc hcpos h_smooth with
    ⟨hcont, hzero, hneg, hsmooth⟩

  have hgenSmooth :
      0 < X.σ ∨ X.BoundedVariation ∨
        ContDiffOn ℝ 2 (vcstar W) (Ioo 0 c) := by
    rcases h_smooth with hσ | hrest
    · exact Or.inl hσ
    · rcases hrest with hbv | htwo
      · exact Or.inr (Or.inl hbv)
      · exact Or.inr (Or.inr (htwo.mono (by
          intro y hy
          exact hy.1)))

  have hhjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
    intro y hy hyc
    have hycR : y < c := by
      exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hctop).mp hyc
    have hgen :=
      generator_vcstar_eq_zero X hX q hq W hW hgenSmooth hcpos y
        ⟨hy, by simpa [c] using hycR⟩
    have hder := vcstar_deriv_ge_one X hX q hq W hW y hy
    refine ⟨hgen.1, ?_⟩
    have hmarg : 1 - deriv (vcstar W) y ≤ 0 := by
      linarith [hder.2]
    simp [hgen.2, hmarg]

  have hver :=
    local_verification X hX q hq (vcstar W) (cstar W) hcpos
      hcont hzero hneg hsmooth hhjb
  have hbelow := hver.1

  have hWc : 0 ≤ W c := hW.2.1 c (le_of_lt hcposR)
  have hdWc : 0 < deriv W c :=
    scaleDeriv_pos X hX q hq W hW c hcposR
  have hvcC : 0 ≤ vcstar W c := by
    simp [vcstar, barrierValue, c, not_lt.mpr (le_of_lt hcposR),
      scaleDeriv, divE, ne_of_gt hcposR]
    exact div_nonneg hWc (le_of_lt hdWc)

  intro x hx
  by_cases hxc : ENNReal.ofReal x ≤ cstar W
  · exact hbelow x hx hxc
  · have hcxE : cstar W < ENNReal.ofReal x := lt_of_not_ge hxc
    have hcx : c < x := by
      exact ENNReal.toReal_lt_of_lt_ofReal hcxE
    have hsplit :
        valueFunctionLe X q (cstar W) x =
          ENNReal.ofReal (x - c) + valueFunctionLe X q (cstar W) c := by
      have h :=
        valueFunctionLe_above_cap X q x c (le_of_lt hcposR) hcx
      simpa [hcap] using h
    have hboundary :
        valueFunctionLe X q (cstar W) c ≤ ENNReal.ofReal (vcstar W c) := by
      apply hbelow c (le_of_lt hcposR)
      exact le_of_eq hcap
    have hstep :
        valueFunctionLe X q (cstar W) x ≤
          ENNReal.ofReal (x - c) + ENNReal.ofReal (vcstar W c) := by
      rw [hsplit]
      exact add_le_add (le_refl _) hboundary
    have hxc_nonneg : 0 ≤ x - c := sub_nonneg.mpr (le_of_lt hcx)
    have hvc_affine : vcstar W x = (x - c) + vcstar W c := by
      simp [vcstar, barrierValue, c, not_lt.mpr hx, not_le.mpr hcx,
        not_lt.mpr (le_of_lt hcposR)]
    calc
      valueFunctionLe X q (cstar W) x
          ≤ ENNReal.ofReal (x - c) + ENNReal.ofReal (vcstar W c) := hstep
      _ = ENNReal.ofReal ((x - c) + vcstar W c) := by
          symm
          exact ENNReal.ofReal_add hxc_nonneg hvcC
      _ = ENNReal.ofReal (vcstar W x) := by rw [hvc_affine]
