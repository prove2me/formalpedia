-- Prove2me | solution 2 for BurkholderDFI.ConcavePhi.theorem_20_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:32:06.895573+00:00
-- url     : https://prove2.me/submissions/975cfa72-afc7-4388-9305-f3c442316235

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Theorems.Thm_BurkholderDFI_ConcavePhi_eq_20_2
import Theorems.Thm_BurkholderDFI_ConcavePhi_truncation_implies_concave

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open BurkholderDFI.ConcavePhi

-- carved from submission 23756e1c-64ee-40aa-88c0-378e6edd0f5e, lines 629-645

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0)
    (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c) (hcc : BurkholderDFI.SquareFnLp.IsConcavePhi Φ) (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) :
    ∫⁻ ω, Φ (∑' k, z (k + 1) ω) ∂P
      ≤ 2 * ∫⁻ ω, Φ (∑' k, condLExp (ℱ k) P (z (k + 1)) ω) ∂P := by
  have hZ : Measurable (fun ω => ∑' k, z (k + 1) ω) :=
    Measurable.ennreal_tsum (fun k => hz (k + 1))
  have hW : Measurable (fun ω => ∑' k, condLExp (ℱ k) P (z (k + 1)) ω) :=
    Measurable.ennreal_tsum (fun k => measurable_condLExp' (ℱ k) P _)
  exact BurkholderDFI.ConcavePhi.truncation_implies_concave Φ c hΦ hcc _ _ hZ hW (fun l hl => BurkholderDFI.ConcavePhi.eq_20_2 ℱ z hz l hl)
