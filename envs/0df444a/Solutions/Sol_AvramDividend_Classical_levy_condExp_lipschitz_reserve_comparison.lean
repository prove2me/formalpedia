-- Prove2me | solution 1 for AvramDividend.Classical.levy_condExp_lipschitz_reserve_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:01:54.611122+00:00
-- url     : https://prove2.me/submissions/fe5153dd-6a96-4ca7-80ab-bc974dccd348

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

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
    P[(fun ω => f (Z ω + (X.X t ω - X.X s ω))) | 𝓕 s] ≤ᵐ[P]
      P[(fun ω => f (W ω + (X.X t ω - X.X s ω)) +
        L * |Z ω - W ω|) | 𝓕 s] ∧
    P[(fun ω => f (W ω + (X.X t ω - X.X s ω))) | 𝓕 s] ≤ᵐ[P]
      P[(fun ω => f (Z ω + (X.X t ω - X.X s ω)) +
        L * |Z ω - W ω|) | 𝓕 s] := by
  have hleZ (ω : Ω) :
      f (Z ω + (X.X t ω - X.X s ω)) ≤
        f (W ω + (X.X t ω - X.X s ω)) +
          L * |Z ω - W ω| := by
    have h := hLip (Z ω + (X.X t ω - X.X s ω))
      (W ω + (X.X t ω - X.X s ω))
    have hc :
        (Z ω + (X.X t ω - X.X s ω)) -
          (W ω + (X.X t ω - X.X s ω)) = Z ω - W ω := by ring
    rw [hc] at h
    have hdiff := le_abs_self
      (f (Z ω + (X.X t ω - X.X s ω)) -
        f (W ω + (X.X t ω - X.X s ω)))
    linarith
  have hleW (ω : Ω) :
      f (W ω + (X.X t ω - X.X s ω)) ≤
        f (Z ω + (X.X t ω - X.X s ω)) +
          L * |Z ω - W ω| := by
    have h := hLip (W ω + (X.X t ω - X.X s ω))
      (Z ω + (X.X t ω - X.X s ω))
    have hc :
        (W ω + (X.X t ω - X.X s ω)) -
          (Z ω + (X.X t ω - X.X s ω)) = W ω - Z ω := by ring
    rw [hc, abs_sub_comm (W ω) (Z ω)] at h
    have hdiff := le_abs_self
      (f (W ω + (X.X t ω - X.X s ω)) -
        f (Z ω + (X.X t ω - X.X s ω)))
    linarith
  exact ⟨condExp_mono hZ (hW.add hDom)
      (Filter.Eventually.of_forall hleZ),
    condExp_mono hW (hZ.add hDom)
      (Filter.Eventually.of_forall hleW)⟩
