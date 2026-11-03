-- Prove2me | solution 4 for AvramDividend.Classical.barrier_cstar_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:46:25.725213+00:00
-- url     : https://prove2.me/submissions/4462337b-3fce-4f5d-a714-4ec6ecb2ad4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_cstar_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_value_of_root_smooth
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_optimal_of_finiteness_attainment_verification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Internal original-source bound, with only local_verification still Open. -/
private theorem w716_direct_bounds {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
    ((∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) := by
  constructor
  · rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ cstar W) with hz | hp
    · have hc0 : cstar W = 0 := hz.symm
      intro x hx
      have hbound := zero_cap_value_upper_bound X hX q hq W hW x hx
      have hvc : vcstar W x = barrierValue W 0 x := by
        change barrierValue W (cstar W).toReal x = barrierValue W 0 x
        simp [hc0]
      simpa only [hc0, hvc] using hbound
    · let c : ℝ := (cstar W).toReal
      have hcast : ENNReal.ofReal c = cstar W :=
        ENNReal.ofReal_toReal (ne_of_lt hc)
      have hcnonneg : 0 ≤ c := ENNReal.toReal_nonneg
      obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
        vcstar_local_verification_regular_of_positive_cstar
          X hX q hq W hW hc hp h_smooth
      have hhjb := vcstar_hjb_below_positive_cstar
        X hX q hq W hW hc h_smooth hp
      have hinside := (local_verification X hX q hq
        (vcstar W) (cstar W) hp hcont hw0 hwneg hsmooth hhjb).1
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
              ENNReal.ofReal (x - c) + valueFunctionLe X q (cstar W) c :=
            hsplit
          _ ≤ ENNReal.ofReal (x - c) + ENNReal.ofReal (vcstar W c) := by
            simpa only [add_comm] using
              (add_le_add_left hval (ENNReal.ofReal (x - c)))
          _ = ENNReal.ofReal ((x - c) + vcstar W c) :=
            (ENNReal.ofReal_add (sub_nonneg.mpr (le_of_lt hcx)) hnonneg).symm
          _ = ENNReal.ofReal (vcstar W x) := by rw [haff]
  · intro hgen
    obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
      vcstar_unrestricted_verification_regularity X hX q hq W hW hc h_smooth
    have hsubset :
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} ⊆ Ioi (0 : ℝ) := by
      intro y hy
      exact hy.1
    have hsmoothTop :
        (¬ X.BoundedVariation →
          ContDiffOn ℝ 2 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
        (X.BoundedVariation →
          ContDiffOn ℝ 1 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) :=
      ⟨fun h => (hsmooth.1 h).mono hsubset,
       fun h => (hsmooth.2 h).mono hsubset⟩
    have hhjbTop :
        ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
          X.GeneratorIntegrable (vcstar W) y ∧
            max (X.generator (vcstar W) y - q * vcstar W y)
                (1 - deriv (vcstar W) y) = 0 := by
      intro y hy _
      exact vcstar_hjb_all_positive_of_generator
        X hX q hq W hW hc h_smooth hgen y hy
    exact (local_verification X hX q hq (vcstar W)
      (⊤ : ℝ≥0∞) ENNReal.zero_lt_top
      hcont hw0 hwneg hsmoothTop hhjbTop).2 rfl

/-- Exact root optimality through its own source-matched local-verification bound. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧
            X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hattain : ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by
    intro x hx
    exact ⟨barrierStrategy_cstar_admissible X hX W hc x hx,
      avram_wave3_02_cstar_value_of_root_smooth
        X hX q hq W hW hc h_smooth x hx⟩
  exact barrier_cstar_optimal_of_finiteness_attainment_verification
    X hX q hq W hW h_smooth hc hattain
    (w716_direct_bounds X hX q hq W hW hc h_smooth)
