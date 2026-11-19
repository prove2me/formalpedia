-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_largeonly_smallmark_L1_budget_positive_gap_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:16:26.131601+00:00
-- url     : https://prove2.me/submissions/c1f914fa-cc40-4be2-a88d-fc46803078c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18_largeonly_original_finitecap_intrinsic_Jmesh_family_zero_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual Jsmall mesh vanishes, so a centred Gaussian gain and disappearing error cannot pay a strict event cash gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνsmall : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (nhds (Jsmall u ω)))
    (σ : Ω → ℝ≥0) (G J E : ℕ → Ω → ℝ)
    (hJmesh : ∀ k : ℕ, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
      (WJ : ℕ → Ω → ℝ),
      ∀ ω : Ω, J k ω =
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω))
    (A : Set Ω) (F : Ω → ℝ) (b δ : ℝ)
    (hδ : 0 < δ)
    (hGcenter : ∀ k, (∫ ω in A, G k ω ∂P) = 0)
    (hBudget : ∀ k, (∫ ω in A, F ω ∂P) ≤
      (∫ ω in A, (fun (_ : Ω) => b) ω ∂P) +
      (∫ ω in A, G k ω ∂P) +
      (∫ ω in A, J k ω ∂P) +
      (∫ ω in A, E k ω ∂P))
    (hEsmall : ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, (∫ ω in A, E k ω ∂P) ≤ ε)
    (hGap : (∫ ω in A, (fun (_ : Ω) => b) ω ∂P) + δ ≤
      (∫ ω in A, F ω ∂P)) :
    False := by
  have hJzero : ∀ k : ℕ, ∀ᵐ ω ∂P, J k ω = 0 :=
    avram_ja18_largeonly_original_finitecap_intrinsic_Jmesh_family_zero_ae
      X hνsmall hLarge Jsmall hJsource σ J hJmesh
  obtain ⟨k, hk⟩ := hEsmall (δ / 2) (by linarith)
  have hJint : (∫ ω in A, J k ω ∂P) = 0 := by
    have hOn : ∀ᵐ ω ∂P.restrict A, J k ω = 0 :=
      ae_restrict_of_ae (hJzero k)
    calc
      (∫ ω in A, J k ω ∂P) = (∫ ω in A, (0 : ℝ) ∂P) :=
        integral_congr_ae hOn
      _ = 0 := by simp
  have hBound := hBudget k
  rw [hGcenter k, hJint] at hBound
  linarith
