-- Prove2me | solution 1 for AvramDividend.Classical.chat04_arbitrary_finite_history_next_increment_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:46:03.239139+00:00
-- url     : https://prove2.me/submissions/ce65dd8d-4d5b-4501-998b-2d63417b4067

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Uniform n-to-(n+1) joint distribution step for ANY number n of
earlier observed future increments and ANY E-valued F_s-measurable
history H. No fixed grid cardinality and no integrability hypotheses.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    {n : ℕ}
    (s u v : ℝ≥0) (hsu : s ≤ u) (huv : u ≤ v)
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ u)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map
      (fun ω => ((H ω, fun i : Fin n => X.X (t i) ω - X.X s ω),
        X.X v ω - X.X u ω)) P =
      (Measure.map
        (fun ω => (H ω, fun i : Fin n => X.X (t i) ω - X.X s ω)) P).prod
          (Measure.map (X.X (v - u)) P) := by
  let Z : Ω → E × (Fin n → ℝ) :=
    fun ω => (H ω, fun i => X.X (t i) ω - X.X s ω)
  have hH_u : Measurable[𝓕 u] H :=
    hH.mono (𝓕.mono hsu) le_rfl
  have hXs_u : Measurable[𝓕 u] (X.X s) :=
    (X.adapted s).mono (𝓕.mono hsu) le_rfl
  have hCoord :
      ∀ i : Fin n, Measurable[𝓕 u]
        (fun ω => X.X (t i) ω - X.X s ω) := by
    intro i
    have hXt_u : Measurable[𝓕 u] (X.X (t i)) :=
      (X.adapted (t i)).mono (𝓕.mono (ht i)) le_rfl
    exact hXt_u.sub hXs_u
  have hVec : Measurable[𝓕 u]
      (fun ω => fun i : Fin n => X.X (t i) ω - X.X s ω) := by
    letI : MeasurableSpace Ω := 𝓕 u
    exact measurable_pi_iff.mpr hCoord
  have hZ : Measurable[𝓕 u] Z := hH_u.prodMk hVec
  simpa only [Z] using
    (AvramDividend.Classical.chat04_past_statistic_future_increment_product_law
      X u v huv Z hZ)
