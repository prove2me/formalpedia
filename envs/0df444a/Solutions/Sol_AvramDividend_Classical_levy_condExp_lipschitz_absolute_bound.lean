-- Prove2me | solution 1 for AvramDividend.Classical.levy_condExp_lipschitz_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:39:01.552246+00:00
-- url     : https://prove2.me/submissions/d0509302-2695-4b18-8a71-16b6f9ed89da

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_reserve_comparison

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
    (s t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z W : Ω → ℝ)
    (hZ : Integrable
      (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hW : Integrable
      (fun ω => f (W ω + (X.X t ω - X.X s ω))) P)
    (hDom : Integrable (fun ω => L * |Z ω - W ω|) P) :
    ∀ᵐ ω ∂P,
      |(P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
        (P[(fun η => f (W η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ≤
      (P[(fun η => L * |Z η - W η|) | 𝓕 s]) ω := by
  have hcomp :=
    levy_condExp_lipschitz_reserve_comparison X s t f L hLip Z W hZ hW hDom
  have haddW := condExp_add hW hDom (𝓕 s)
  have haddZ := condExp_add hZ hDom (𝓕 s)
  filter_upwards [hcomp.1, hcomp.2, haddW, haddZ] with ω hleZ hleW heqW heqZ
  change
    (P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
    (P[((fun η => f (W η + (X.X t η - X.X s η))) +
      (fun η => L * |Z η - W η|)) | 𝓕 s]) ω at hleZ
  change
    (P[(fun η => f (W η + (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
    (P[((fun η => f (Z η + (X.X t η - X.X s η))) +
      (fun η => L * |Z η - W η|)) | 𝓕 s]) ω at hleW
  rw [heqW] at hleZ
  rw [heqZ] at hleW
  simp only [Pi.add_apply] at hleZ hleW
  exact abs_le.mpr ⟨by linarith, by linarith⟩