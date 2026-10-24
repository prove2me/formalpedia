-- Prove2me | solution 1 for AvramDividend.Classical.chat01_unbounded_killed_martingale_of_condExp_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:50:06.413884+00:00
-- url     : https://prove2.me/submissions/e3a3c7b6-e7f0-4e73-8be2-d45b28fccd10

import Mathlib.Probability.Martingale.Basic
import Mathlib.Data.Nat.Pairing
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_payoff_adapted
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-- Under unbounded variation, the killed-scale martingale follows from
its conditional-expectation identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (Z : ℝ≥0 → Ω → ℝ)
    (hZ : Z = fun t ω =>
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω)) ω)
    (hCond : ∀ s u : ℝ≥0, s ≤ u →
      P[Z u | 𝓕 s] =ᵐ[P] Z s) :
    Martingale Z 𝓕 P := by
  have hAdapted : Adapted 𝓕 Z := by
    subst Z
    exact chat03_killed_scale_payoff_adapted X
      (fun j : ℕ =>
        ((Nat.unpair j).2 : ℝ≥0) *
          ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹))
      (by
        intro n hn k
        exact chat04_nat_pairing_rational_grid_coverage n k hn)
      q x W hW
  have hStrong : StronglyAdapted 𝓕 Z :=
    hAdapted.stronglyAdapted
  refine ⟨hStrong, ?_⟩
  intro s u hsu
  exact hCond s u hsu
