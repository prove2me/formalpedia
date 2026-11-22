-- Prove2me | solution 1 for FiniteEnergyPlane.dlambdaEnergy_ne_top_of_univ_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T19:43:09.039243+00:00
-- url     : https://prove2.me/submissions/cc654b77-8a82-45e1-986d-fda629932d8b

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib



/-! dλ-energy bookkeeping on discs. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem dlambdaEnergy_ne_top_of_univ_eq_ofReal_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (T : ℝ)
    (htot : dlambdaEnergy H Set.univ u = ENNReal.ofReal T) (s : Set ℂ) :
    dlambdaEnergy H s u ≠ ⊤ := by
  have h : dlambdaEnergy H s u ≤ dlambdaEnergy H Set.univ u :=
    lintegral_mono_set (Set.subset_univ _)
  exact ne_top_of_le_ne_top (by rw [htot]; exact ENNReal.ofReal_ne_top) h

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (T : ℝ)
    (htot : dlambdaEnergy H Set.univ u = ENNReal.ofReal T) (s : Set ℂ) :
    dlambdaEnergy H s u ≠ ⊤ :=
  FiniteEnergyPlane.dlambdaEnergy_ne_top_of_univ_eq_ofReal_aux H u T htot s
