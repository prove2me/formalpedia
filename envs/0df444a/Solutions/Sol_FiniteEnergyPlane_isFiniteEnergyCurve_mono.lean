-- Prove2me | solution 1 for FiniteEnergyPlane.isFiniteEnergyCurve_mono
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T19:51:21.112306+00:00
-- url     : https://prove2.me/submissions/5c6422f9-8504-43e5-9212-be2103145285

import Definitions.Def_FiniteEnergyPlane_Setting



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The restriction of a finite-energy curve on `U` to a subset `W ⊆ U` is a finite-energy curve
on `W`, with Hofer energy and `dλ`-energy on `W` at most those on `U`. -/
theorem isFiniteEnergyCurve_mono {n : ℕ} (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (U W : Set ℂ)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (hWU : W ⊆ U) :
    IsFiniteEnergyCurve H J W u ∧ energy H W u ≤ energy H U u ∧
      dlambdaEnergy H W u ≤ dlambdaEnergy H U u := by
  have hE : energy H W u ≤ energy H U u :=
    iSup₂_mono fun φ _ => lintegral_mono_set hWU
  exact ⟨⟨hu.1.mono hWU, fun z hz => hu.2.1 z (hWU hz), fun z hz => hu.2.2.1 z (hWU hz),
    hE.trans_lt hu.2.2.2⟩, hE, lintegral_mono_set hWU⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (U W : Set ℂ)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (hWU : W ⊆ U) :
    IsFiniteEnergyCurve H J W u ∧ energy H W u ≤ energy H U u ∧
      dlambdaEnergy H W u ≤ dlambdaEnergy H U u :=
  isFiniteEnergyCurve_mono H J U W u hu hWU
