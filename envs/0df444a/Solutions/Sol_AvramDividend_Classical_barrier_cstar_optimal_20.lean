-- Prove2me | solution 20 for AvramDividend.Classical.barrier_cstar_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:47:06.461182+00:00
-- url     : https://prove2.me/submissions/7842dcc4-8733-42c7-884e-117b62cda0de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_cstar_original_capped_optimality
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_positive_cap_interior_HJB
import Theorems.Thm_AvramDividend_Classical_admissible_cap_dividendValue_le
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_strategywise_cap_budget_to_both_values
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
import Theorems.Thm_AvramDividend_Classical_avram_sweep19_vcstar_top_original_verification_hypotheses
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_root_optimality_of_original_verification_pair
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by
  have hc : cstar W < (⊤ : ℝ≥0∞) :=
    AvramDividend.Classical.cstar_lt_top X hX q hq W hW
  have hCap : ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
    by_cases hz : cstar W = 0
    · intro x hx
      exact le_of_eq
        (AvramDividend.Classical.avram_sweep16_zero_cstar_original_capped_optimality
          X hX q hq W hW hz x hx)
    · have hcpos : (0 : ℝ≥0∞) < cstar W :=
        lt_of_le_of_ne (by simp) (Ne.symm hz)
      obtain ⟨hCont, hV0, hNeg, hSmooth⟩ :=
        AvramDividend.Classical.vcstar_local_verification_regular_of_positive_cstar
          X hX q hq W hW hc hcpos h_smooth
      have hHJB :=
        AvramDividend.Classical.avram_sweep17_vcstar_positive_cap_interior_HJB
          X hX q hq W hW hc hcpos h_smooth
      have hStrategy : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
          ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x (cstar W) D →
            dividendValue X q x D ≤ ENNReal.ofReal (vcstar W x) := by
        intro x hx hxc D hD
        exact AvramDividend.Classical.admissible_cap_dividendValue_le
          X hX q hq (vcstar W) (cstar W) hcpos
          hCont hV0 hNeg hSmooth hHJB x hx hxc D hD
      have hLocal :=
        (AvramDividend.Classical.avram_sweep16_original_strategywise_cap_budget_to_both_values
          X q (vcstar W) (cstar W) hStrategy).1
      exact
        AvramDividend.Classical.avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
          X hX q hq W hW hc h_smooth hLocal
  have hUncap :
      (∀ y : ℝ, (cstar W).toReal < y →
        X.GeneratorIntegrable (vcstar W) y ∧
          X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x) := by
    intro hgen x hx
    obtain ⟨hCont, hV0, hNeg, hSmooth, hHJB⟩ :=
      AvramDividend.Classical.avram_sweep19_vcstar_top_original_verification_hypotheses
        X hX q hq W hW hc h_smooth hgen
    have hStrategyTop :
        ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ (⊤ : ℝ≥0∞) →
          ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x ⊤ D →
            dividendValue X q x D ≤ ENNReal.ofReal (vcstar W x) := by
      intro x hx hxc D hD
      exact AvramDividend.Classical.admissible_cap_dividendValue_le
        X hX q hq (vcstar W) ⊤ (by simp)
        hCont hV0 hNeg hSmooth hHJB x hx hxc D hD
    exact
      (AvramDividend.Classical.avram_sweep16_original_strategywise_cap_budget_to_both_values
        X q (vcstar W) (⊤ : ℝ≥0∞) hStrategyTop).2 rfl x hx
  exact
    AvramDividend.Classical.avram_sweep16_root_optimality_of_original_verification_pair
      X hX q hq W hW ⟨hCap, hUncap⟩
