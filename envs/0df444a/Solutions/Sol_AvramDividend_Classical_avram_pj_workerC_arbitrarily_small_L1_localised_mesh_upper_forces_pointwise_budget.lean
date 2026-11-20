-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_arbitrarily_small_L1_localised_mesh_upper_forces_pointwise_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:31:31.712041+00:00
-- url     : https://prove2.me/submissions/bde9701e-6e99-464e-a9aa-69bc71149aa7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (V U : Ω → ℝ)
    (hGap : Integrable (fun ω => V ω - U ω) P)
    (hSource : ∀ ε : ℝ, 0 < ε →
      ∃ (K : Ω → ℝ) (E : ℕ → Ω → ℝ),
        Integrable K P ∧
        (∫ ω, |K ω| ∂P) ≤ ε ∧
        (∀ k, Integrable (E k) P) ∧
        (∀ k, ∀ᵐ ω ∂P, V ω - U ω ≤ K ω + E k ω) ∧
        Tendsto (fun k : ℕ => ∫ ω, |E k ω| ∂P)
          atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P, V ω ≤ U ω := by
  have hPosI :
      Integrable (fun ω => max (0 : ℝ) (V ω - U ω)) P := by
    convert hGap.pos_part using 1
    funext ω
    simp [max_comm]
  have hNonneg :
      ∀ᵐ ω ∂P, 0 ≤ max (0 : ℝ) (V ω - U ω) :=
    Filter.Eventually.of_forall (fun ω => le_max_left _ _)
  have hSmall (ε : ℝ) (hε : 0 < ε) :
      (∫ ω, max (0 : ℝ) (V ω - U ω) ∂P) ≤ ε := by
    obtain ⟨K, E, hKI, hKsmall, hEI, hBound, hVan⟩ := hSource ε hε
    have hEvery (k : ℕ) :
        (∫ ω, max (0 : ℝ) (V ω - U ω) ∂P) ≤
          (∫ ω, |K ω| ∂P) + (∫ ω, |E k ω| ∂P) := by
      have hDom : ∀ᵐ ω ∂P,
          max (0 : ℝ) (V ω - U ω) ≤ |K ω| + |E k ω| := by
        filter_upwards [hBound k] with ω hω
        apply max_le
        · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
        · exact hω.trans (add_le_add (le_abs_self _) (le_abs_self _))
      have hI : Integrable (fun ω => |K ω| + |E k ω|) P :=
        hKI.abs.add (hEI k).abs
      simpa only [integral_add hKI.abs (hEI k).abs] using
        (integral_mono_ae hPosI hI hDom)
    have hLim :
        Tendsto
          (fun k : ℕ => (∫ ω, |K ω| ∂P) + (∫ ω, |E k ω| ∂P))
          atTop (𝓝 ((∫ ω, |K ω| ∂P) + 0)) :=
      tendsto_const_nhds.add hVan
    have hBounded :
        (∫ ω, max (0 : ℝ) (V ω - U ω) ∂P) ≤
          (∫ ω, |K ω| ∂P) := by
      have h := ge_of_tendsto hLim
        (Filter.Eventually.of_forall hEvery)
      simpa only [add_zero] using h
    exact hBounded.trans hKsmall
  have hIntNonneg :
      0 ≤ (∫ ω, max (0 : ℝ) (V ω - U ω) ∂P) :=
    integral_nonneg (fun _ => le_max_left _ _)
  have hIntZero :
      (∫ ω, max (0 : ℝ) (V ω - U ω) ∂P) = 0 := by
    have hLe : (∫ ω, max (0 : ℝ) (V ω - U ω) ∂P) ≤ 0 := by
      by_contra hnot
      have hp : 0 < (∫ ω, max (0 : ℝ) (V ω - U ω) ∂P) :=
        lt_of_not_ge hnot
      have hHalf := hSmall _ (half_pos hp)
      linarith
    exact le_antisymm hLe hIntNonneg
  have hAE :
      (fun ω => max (0 : ℝ) (V ω - U ω)) =ᵐ[P] (fun _ => 0) :=
    (integral_eq_zero_iff_of_nonneg_ae hNonneg hPosI).mp hIntZero
  filter_upwards [hAE] with ω hω
  have hMax : max (0 : ℝ) (V ω - U ω) = 0 := hω
  have hLe : V ω - U ω ≤ 0 :=
    (le_max_right (0 : ℝ) (V ω - U ω)).trans_eq hMax
  linarith
