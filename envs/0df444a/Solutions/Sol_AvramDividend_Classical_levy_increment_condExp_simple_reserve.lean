-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_simple_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:38:46.698999+00:00
-- url     : https://prove2.me/submissions/ff9209ef-ccc4-4f6d-948e-f94023d853f6

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Data.Fintype.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_valued_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (S : SimpleFunc Ω ℝ)
    (hS : Measurable[𝓕 s] (S : Ω → ℝ))
    (f : ℝ → ℝ) (hf : Measurable f)
    (hI : ∀ r ∈ Set.range (S : Ω → ℝ),
      Integrable (fun ω => f (r + X.X (t - s) ω)) P) :
    P[(fun ω => f (S ω + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (S ω + X.X (t - s) η) ∂P) := by
  classical
  letI : Fintype (Set.range (S : Ω → ℝ)) := S.finite_range.fintype
  let p : Ω → Set.range (S : Ω → ℝ) :=
    fun ω => ⟨S ω, ⟨ω, rfl⟩⟩
  have hp (i : Set.range (S : Ω → ℝ)) :
      MeasurableSet[𝓕 s] {ω : Ω | p ω = i} := by
    have heq :
        {ω : Ω | p ω = i} =
          (S : Ω → ℝ) ⁻¹' ({i.1} : Set ℝ) := by
      ext ω
      simp [p, Subtype.ext_iff]
    rw [heq]
    exact hS (measurableSet_singleton i.1)
  have hIntegrable (i : Set.range (S : Ω → ℝ)) :
      Integrable (fun ω => f (i.1 + X.X (t - s) ω)) P :=
    hI i.1 i.2
  have hCE :=
    levy_increment_condExp_finite_valued_reserve X s t hst
      p hp (fun i : Set.range (S : Ω → ℝ) => i.1)
      f hf hIntegrable
  simpa only [p] using hCE
