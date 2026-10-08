-- Prove2me | solution 2 for AvramDividend.Classical.barrier_cstar_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:41:23.919796+00:00
-- url     : https://prove2.me/submissions/2c61b4ff-0f3e-4be1-af0f-89c5cd64202f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_verification_upper_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  have hc : cstar W < ⊤ :=
    (AvramDividend.Classical.cstar_optimal_barrier X hX q hq W hW).1
  have hattain :=
    AvramDividend.Classical.barrier_cstar_attains_value_all_capital
      X hX q hq W hW hc
  obtain ⟨hcapUpper, hglobalUpper⟩ :=
    AvramDividend.Classical.barrier_cstar_verification_upper_bounds
      X hX q hq W hW hc h_smooth
  refine ⟨hc, ?_, ?_⟩
  · intro x hx
    obtain ⟨hcap, hvalue⟩ := hattain x hx
    refine ⟨hcap, hvalue, ?_⟩
    apply le_antisymm (hcapUpper x hx)
    calc
      ENNReal.ofReal (vcstar W x) =
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) := hvalue.symm
      _ ≤ valueFunctionLe X q (cstar W) x := by
        unfold valueFunctionLe
        exact le_iSup_of_le (barrierStrategy X x (cstar W).toReal)
          (le_iSup_of_le hcap (le_refl _))
  · intro hgen x hx
    obtain ⟨hcap, hvalue⟩ := hattain x hx
    refine ⟨hcap.1, ?_⟩
    apply le_antisymm (hglobalUpper hgen x hx)
    calc
      ENNReal.ofReal (vcstar W x) =
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) := hvalue.symm
      _ ≤ valueFunction X q x := by
        unfold valueFunction
        exact le_iSup_of_le (barrierStrategy X x (cstar W).toReal)
          (le_iSup_of_le hcap.1 (le_refl _))
