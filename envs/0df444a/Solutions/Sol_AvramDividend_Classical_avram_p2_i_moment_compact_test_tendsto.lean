-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_compact_test_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:50:44.115845+00:00
-- url     : https://prove2.me/submissions/87ef8fe4-0a24-44d5-96bd-4048a59a3e35

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_envelope_test_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_weierstrass_with_tail
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_global_poly_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped BigOperators ENNReal

theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hfinite_i : ∀ i, (μi i) Set.univ < ⊤)
    (hfinite_μ : μ Set.univ < ⊤)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : ∀ k,
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by
  have hgi (i : ι) : Integrable g (μi i) :=
    AvramDividend.Classical.avram_p2_i_moment_compact_test_integrable
      (μi i) (hfinite_i i) g hg hg0
  have hgμ : Integrable g μ :=
    AvramDividend.Classical.avram_p2_i_moment_compact_test_integrable
      μ hfinite_μ g hg hg0
  have hpositive (i : ι) : ∀ᵐ z ∂μi i, 0 ≤ z :=
    (hpositive_i i).mono (fun z hz => le_of_lt hz)
  have happrox (γ : ℝ) (hγ : 0 < γ) :
      ∃ p : Polynomial ℝ, ∃ K : ℕ,
        ∀ z : ℝ, 0 ≤ z →
          |g z - p.eval z| ≤ γ * (1 + z ^ K) := by
    obtain ⟨p, hp, ⟨K, hK, htail⟩⟩ :=
      AvramDividend.Classical.avram_p2_i_moment_weierstrass_with_tail
        g hg.continuousOn γ hγ
    refine ⟨p, K, ?_⟩
    exact AvramDividend.Classical.avram_p2_i_moment_global_poly_envelope
      g p γ (le_of_lt hγ) K
      (fun z hz => hg0 z (Or.inr hz))
      (fun z hz => le_of_lt (hp z hz)) htail
  exact AvramDividend.Classical.avram_p2_i_moment_envelope_test_tendsto
    l μi μ hpositive hunit_μ hi hμ hmom g hgi hgμ happrox
