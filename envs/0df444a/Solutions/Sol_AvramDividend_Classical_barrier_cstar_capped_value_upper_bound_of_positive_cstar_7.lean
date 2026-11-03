-- Prove2me | solution 7 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:49:25.905737+00:00
-- url     : https://prove2.me/submissions/0fbcc17d-d4e8-4e74-91e1-db1d5b05517e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_core_positive_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zero_horizon_bound
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_truncated_hjb_budget
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital

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
  have hcast : ENNReal.ofReal c = cstar W :=
    ENNReal.ofReal_toReal (ne_of_lt hc)
  have hcnonneg : 0 ≤ c := ENNReal.toReal_nonneg
  obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
    vcstar_local_verification_regular_of_positive_cstar
      X hX q hq W hW hc hcpos h_smooth
  have hhjb := vcstar_hjb_below_positive_cstar
    X hX q hq W hW hc h_smooth hcpos
  have hverification :=
    local_verification_from_uniform_truncated_hjb_budget
      X q (vcstar W) (cstar W) (by
        intro y hy hyc D hD n
        obtain ⟨hgen, hgrad, hnonneg, hjump⟩ :=
          local_verification_stochastic_core_side_conditions
            X q (vcstar W) (cstar W)
            hcont hw0 hsmooth hhjb y hyc D hD
        by_cases hBV : X.BoundedVariation
        · exact admissible_cap_truncated_bv_stochastic_core_positive_cap
            X hX hBV q hq (vcstar W) (cstar W) hcpos
            hcont hw0 hwneg (hsmooth.2 hBV) hgen hgrad
            y hy hyc D hD hnonneg hjump
            (n : ℝ) (Nat.cast_nonneg n)
        · by_cases hyzero : y = 0
          · subst y
            exact avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
              X hBV q (vcstar W) (cstar W)
              hw0 hcont (hsmooth.1 hBV) hgrad
              D hD hjump (n : ℝ) (Nat.cast_nonneg n)
          · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hyzero)
            by_cases hnzero : n = 0
            · subst n
              have hC1 : ContDiffOn ℝ 1 (vcstar W)
                  {z : ℝ | 0 < z ∧ ENNReal.ofReal z < cstar W} :=
                (hsmooth.1 hBV).of_le (by norm_num)
              simpa only [Nat.cast_zero] using
                (avram_wave3_04_corrected_ubv_zero_horizon_bound
                  X q y (vcstar W) (cstar W)
                  hw0 hcont hC1 hgrad D hD hyc hjump)
            · have hnpos : 0 < (n : ℝ) := by
                exact_mod_cast Nat.pos_of_ne_zero hnzero
              exact avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
                X hX hBV q hq (vcstar W) (cstar W) hcpos
                hw0 hcont hwneg (hsmooth.1 hBV) hgen hgrad
                y hypos hyc D hD hnonneg hjump (n : ℝ) hnpos)
  have hinside := hverification.1
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
