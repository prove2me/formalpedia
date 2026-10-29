-- Prove2me | solution 1 for AvramDividend.Classical.ae_rogozin_slopes_of_gaussian_component
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T21:50:53.464115+00:00
-- url     : https://prove2.me/submissions/6244b0f3-3338-4f9e-a112-cf76805dbf88

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_three_mgf_strict_gap_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_gaussian_grid_uniform_negative_mass_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_germ_negative_limsup_ae_of_uniform_mass_ws01f

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Filter Topology
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : 0 < X.σ) :
    ∀ᵐ ω ∂P, ∀ C : ℝ,
      ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
        X.X t ω < C * (t : ℝ) := by
  haveI := X.isProbability
  have ha : 0 < X.σ ^ 2 / 2 := by positivity
  obtain ⟨m, hm, hgap⟩ :=
    gaussian_three_mgf_strict_gap_ws01f (X.σ ^ 2 / 2) ha
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  let δ : ℕ → ℝ≥0 := fun n =>
    ⟨1 / (((m : ℝ) * ((n : ℝ) + 1)) ^ 2), by positivity⟩
  have hδformula (n : ℕ) :
      (δ n : ℝ) = 1 / (((m : ℝ) * ((n : ℝ) + 1)) ^ 2) := rfl
  have hδpos (n : ℕ) : 0 < δ n := by
    apply NNReal.coe_pos.mp
    rw [hδformula]
    positivity
  have hdiv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hδreal :
      Tendsto (fun n : ℕ => (δ n : ℝ)) atTop (𝓝 0) := by
    have hh := (hdiv.pow 2).const_mul (1 / (m : ℝ) ^ 2)
    have hlim :
        Tendsto
          (fun n : ℕ => (1 / (m : ℝ) ^ 2) *
            ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2)
          atTop (𝓝 0) := by simpa using hh
    convert hlim using 1
    ext n
    rw [hδformula]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp [ne_of_gt hmR, ne_of_gt hn] <;> ring
  have hδzero : Tendsto δ atTop (𝓝 (0 : ℝ≥0)) :=
    (NNReal.tendsto_coe).mp hδreal
  have hδwithin :
      Tendsto δ atTop (nhdsWithin (0 : ℝ≥0) (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hδzero, Filter.Eventually.of_forall (fun n => hδpos n)⟩
  have hEach (k : ℕ) :
      ∀ᵐ ω ∂P,
        ω ∈ (⋂ j : ℕ, ⋃ n : ℕ,
          {ω : Ω | j ≤ n ∧
            X.X (δ n) ω < -(k : ℝ) * (δ n : ℝ)}) := by
    obtain ⟨p, hp, N, hN⟩ :=
      levy_gaussian_grid_uniform_negative_mass_ws01f
        X m hm (-(k : ℝ)) δ hδformula hgap
    exact levy_germ_negative_limsup_ae_of_uniform_mass_ws01f
      X δ hδzero (-(k : ℝ)) p hp N hN
  have hAll :
      ∀ᵐ ω ∂P, ∀ k : ℕ,
        ω ∈ (⋂ j : ℕ, ⋃ n : ℕ,
          {ω : Ω | j ≤ n ∧
            X.X (δ n) ω < -(k : ℝ) * (δ n : ℝ)}) :=
    ae_all_iff.mpr hEach
  filter_upwards [hAll] with ω hω
  intro C
  obtain ⟨k, hk⟩ := exists_nat_gt (-C)
  have hSlope : -(k : ℝ) < C := by linarith
  change ¬ ∀ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
    ¬ X.X t ω < C * (t : ℝ)
  intro hNo
  have hNoSeq : ∀ᶠ n in atTop,
      ¬ X.X (δ n) ω < C * (δ n : ℝ) :=
    hδwithin.eventually hNo
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hNoSeq
  obtain ⟨n, hn⟩ :=
    Set.mem_iUnion.mp ((Set.mem_iInter.mp (hω k)) N)
  have htime : (0 : ℝ) < (δ n : ℝ) := by
    exact_mod_cast hδpos n
  have hbound : -(k : ℝ) * (δ n : ℝ) < C * (δ n : ℝ) :=
    mul_lt_mul_of_pos_right hSlope htime
  exact (hN n hn.1) (lt_trans hn.2 hbound)
