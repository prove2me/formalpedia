-- Prove2me | solution 11 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:12:56.265441+00:00
-- url     : https://prove2.me/submissions/e2d7bc80-a8e3-43dc-b0e0-4b2098ab7e86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
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
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hc0 : cstar W ≠ 0 := ne_of_gt hcpos
  have hcrealpos : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos hc0 hctop
  have hcreal0 : 0 ≤ (cstar W).toReal := le_of_lt hcrealpos
  have hsmooth_inner :
      0 < X.σ ∨ X.BoundedVariation ∨
        ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal) := by
    rcases h_smooth with hσ | hBV | hC2
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hBV)
    · exact Or.inr (Or.inr (hC2.mono (by
        intro z hz
        exact hz.1)))
  obtain ⟨hcont, hv0, hneg, hsmoothV⟩ :=
    AvramDividend.Classical.vcstar_local_verification_regular_of_positive_cstar
      X hX q hq W hW hc hcpos h_smooth
  have hhjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
    intro y hy hyl
    have hylt : y < (cstar W).toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hctop).mp hyl
    have hgen :=
      AvramDividend.Classical.generator_vcstar_eq_zero
        X hX q hq W hW hsmooth_inner hcpos y ⟨hy, hylt⟩
    have hder :=
      AvramDividend.Classical.vcstar_deriv_ge_one X hX q hq W hW y hy
    refine ⟨hgen.1, ?_⟩
    rw [hgen.2]
    exact max_eq_left (sub_nonpos.mpr hder.2)
  have hver :=
    AvramDividend.Classical.local_verification
      X hX q hq (vcstar W) (cstar W) hcpos
      hcont hv0 hneg hsmoothV hhjb
  have hlocal := hver.1
  have hceq : ENNReal.ofReal (cstar W).toReal = cstar W :=
    ENNReal.ofReal_toReal hctop
  have hWc : 0 ≤ W (cstar W).toReal :=
    hW.2.1 _ hcreal0
  have hdc : 0 ≤ deriv W (cstar W).toReal :=
    AvramDividend.Classical.scaleDeriv_nonneg
      X q W hW _ hcrealpos
  have hvc : 0 ≤ vcstar W (cstar W).toReal := by
    simp only [vcstar, barrierValue, not_lt.mpr hcreal0, if_false, le_rfl, if_true]
    simp [scaleDeriv, divE, ne_of_gt hcrealpos]
    exact div_nonneg hWc hdc
  intro x hx
  by_cases hxcap : ENNReal.ofReal x ≤ cstar W
  · exact hlocal x hx hxcap
  · have hgt : cstar W < ENNReal.ofReal x := lt_of_not_ge hxcap
    have hcx : (cstar W).toReal < x :=
      (ENNReal.lt_ofReal_iff_toReal_lt hctop).mp hgt
    have hboundary :
        valueFunctionLe X q (cstar W) (cstar W).toReal ≤
          ENNReal.ofReal (vcstar W (cstar W).toReal) := by
      exact hlocal _ hcreal0 (le_of_eq hceq)
    have habove :=
      AvramDividend.Classical.valueFunctionLe_above_cap
        X q x (cstar W).toReal hcreal0 hcx
    have hdelta : 0 ≤ x - (cstar W).toReal := sub_nonneg.mpr (le_of_lt hcx)
    have haffine :
        vcstar W x =
          x - (cstar W).toReal + vcstar W (cstar W).toReal := by
      simp [vcstar, barrierValue, not_lt.mpr hx, not_lt.mpr hcreal0,
        not_le.mpr hcx]
    calc
      valueFunctionLe X q (cstar W) x =
          ENNReal.ofReal (x - (cstar W).toReal) +
            valueFunctionLe X q (cstar W) (cstar W).toReal := by
        simpa [hceq] using habove
      _ ≤ ENNReal.ofReal (x - (cstar W).toReal) +
            ENNReal.ofReal (vcstar W (cstar W).toReal) :=
        add_le_add (le_refl _) hboundary
      _ = ENNReal.ofReal (vcstar W x) := by
        rw [← ENNReal.ofReal_add hdelta hvc, haffine]
