-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_martingale_of_condExp_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:30:12.909068+00:00
-- url     : https://prove2.me/submissions/37984374-61ae-4c47-8154-b25e2e2f8056

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_martingale_regularities

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! The killed-scale martingale follows from its conditional-expectation
identity, using the accepted adaptedness theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (Z : ℝ≥0 → Ω → ℝ)
    (hZ : Z = fun t ω =>
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω)) ω)
    (hCond : ∀ s u : ℝ≥0, s ≤ u →
      P[Z u | 𝓕 s] =ᵐ[P] Z s) :
    Martingale Z 𝓕 P := by
  have hReg :=
    chat03_killed_scale_martingale_regularities
      X hX q hq W hW x
  have hAdapted : Adapted 𝓕 Z := by
    subst Z
    exact hReg.1
  have hStronglyAdapted : StronglyAdapted 𝓕 Z :=
    hAdapted.stronglyAdapted
  refine ⟨hStronglyAdapted, ?_⟩
  intro s u hsu
  exact hCond s u hsu
