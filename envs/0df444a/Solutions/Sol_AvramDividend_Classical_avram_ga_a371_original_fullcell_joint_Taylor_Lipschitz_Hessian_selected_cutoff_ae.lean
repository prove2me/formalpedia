-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a371_original_fullcell_joint_Taylor_Lipschitz_Hessian_selected_cutoff_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:22:11.429693+00:00
-- url     : https://prove2.me/submissions/60c76ae3-492c-4e38-aba8-857bfee1b26f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a194_original_fullcell_small_Taylor_positive_raw_square_control
import Theorems.Thm_AvramDividend_Classical_avram_ga_a369_original_fullcell_small_raw_increment_local_postpayment_Lipschitz_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a370_original_fullcell_unweighted_postpayment_Hessian_uniform_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hTopCap : C = ⊤) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        s < ρ ω → s + Δ ≤ ρ ω → |r| < δ →
          max (Real.exp (-(q * (s : ℝ))) *
            (w (y + r) - w y - deriv w y * r -
              iteratedDeriv 2 w y / 2 * r^2)) 0 ≤ ε * r^2 ∧
          |w (y + r) - w y| ≤ L * |r| ∧
          |iteratedDeriv 2 w y| ≤ M := by
  obtain ⟨δL,hδL,L,hL,hLip⟩ :=
    avram_ga_a369_original_fullcell_small_raw_increment_local_postpayment_Lipschitz_ae
      X x hx D hD w C hTopCap hw n ρ j hprefix
  obtain ⟨M,hM,hHess⟩ :=
    avram_ga_a370_original_fullcell_unweighted_postpayment_Hessian_uniform_ae
      X x hx D hD w C hTopCap hw n ρ j hprefix
  refine ⟨L,M,hL,hM,?_⟩
  intro ε hε
  obtain ⟨δT,hδT,hTaylor⟩ :=
    avram_ga_a194_original_fullcell_small_Taylor_positive_raw_square_control
      X x hx D hD C hTopCap w hw q hq n ρ j hprefix ε hε
  refine ⟨min δT δL,lt_min hδT hδL,?_⟩
  filter_upwards [hTaylor,hLip,hHess] with ω ht hl hh
  intro m i
  dsimp
  intro hs he hr
  have hrT : |X.X ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
      (n : ℝ≥0) / ((m : ℝ≥0) + 1)) ω -
    X.X ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω| < δT :=
    lt_of_lt_of_le hr (min_le_left _ _)
  have hrL : |X.X ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
      (n : ℝ≥0) / ((m : ℝ≥0) + 1)) ω -
    X.X ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω| < δL :=
    lt_of_lt_of_le hr (min_le_right _ _)
  exact ⟨ht m i hs he hrT,hl m i hs hrL,hh m i hs⟩
