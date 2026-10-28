-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_discounted_scale_unstopped_martingale_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:31:18.955151+00:00
-- url     : https://prove2.me/submissions/3a48d19f-5799-4445-9a73-03ee8a15851a

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_unstopped_scale_martingale_forces_nonpositive_paths
import Theorems.Thm_AvramDividend_Classical_positive_psi_excludes_nonpositive_one_increment_ae
import Mathlib.Probability.Martingale.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The un-killed discounted scale reward cannot be a martingale for any
unbounded-variation Lévy process and positive discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ¬ Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P := by
  intro hMart
  have hWzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hStart : ∀ᵐ ω ∂P, X.X 0 ω = 0 :=
    Filter.Eventually.of_forall X.X_zero
  have hNonpos : ∀ᵐ ω ∂P, X.X 1 ω ≤ 0 :=
    unbounded_unstopped_scale_martingale_forces_nonpositive_paths
      X q W hW hnbv hWzero hStart hMart (1 : ℝ≥0)
  obtain ⟨β₀, hβ₀, hlarge⟩ :=
    chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  have hψ : 0 < X.ψ β₀ := lt_trans hq (hlarge β₀ le_rfl)
  exact positive_psi_excludes_nonpositive_one_increment_ae
    X β₀ hβ₀ hψ hNonpos
