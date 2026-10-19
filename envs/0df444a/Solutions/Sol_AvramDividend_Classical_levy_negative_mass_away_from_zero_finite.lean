-- Prove2me | solution 1 for AvramDividend.Classical.levy_negative_mass_away_from_zero_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:06:25.228369+00:00
-- url     : https://prove2.me/submissions/c8eb767a-549c-4924-9743-d829d4a3daa2

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ) (hδ : 0 < δ) :
    X.ν (Iic (-δ)) < ⊤ := by
  let k : ℝ := min 1 (δ ^ 2)
  let F : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (min 1 (y ^ 2))
  have hk : 0 < k := by
    dsimp [k]
    exact lt_min (by norm_num) (sq_pos_of_pos hδ)
  have hcpos : 0 < ENNReal.ofReal k := ENNReal.ofReal_pos.mpr hk
  have hctop : ENNReal.ofReal k < ⊤ := ENNReal.ofReal_lt_top
  have hm : AEMeasurable F X.ν := by
    unfold F
    fun_prop
  have hfloor : ∀ y ∈ Iic (-δ), ENNReal.ofReal k ≤ F y := by
    intro y hy
    have hn : 0 ≤ -y - δ := by
      change y ≤ -δ at hy
      linarith
    have hn' : 0 ≤ -y + δ := by linarith
    have hsq : δ ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_nonneg hn hn']
    have hmin : k ≤ min 1 (y ^ 2) := min_le_min le_rfl hsq
    exact ENNReal.ofReal_le_ofReal hmin
  have hsubset : Iic (-δ) ⊆ {y | ENNReal.ofReal k ≤ F y} := hfloor
  have hmarkov : X.ν (Iic (-δ)) ≤ (∫⁻ y, F y ∂X.ν) / ENNReal.ofReal k :=
    (measure_mono hsubset).trans
      (meas_ge_le_lintegral_div hm hcpos.ne' hctop.ne)
  exact lt_of_le_of_lt hmarkov
    (ENNReal.div_lt_top X.ν_integrable.ne hcpos.ne')