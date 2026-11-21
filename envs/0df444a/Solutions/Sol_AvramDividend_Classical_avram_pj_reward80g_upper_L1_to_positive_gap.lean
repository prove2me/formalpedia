-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward80g_upper_L1_to_positive_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:10:42.736253+00:00
-- url     : https://prove2.me/submissions/12739595-17eb-4996-ac2e-017b049137a7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward79_two_stage_cutoff_mesh_signed_L1_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G U V : Ω → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ) (E : ℕ → Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, V ω - U ω ≤ K ω + E k ω) ∧
      Tendsto (fun k : ℕ => ∫ ω, |E k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P,
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by
  obtain ⟨K, E, hKI, hKsmall, hEI, hUpper, hVan⟩ := hSource
  have hQ : ∀ k : ℕ, ∀ᵐ ω ∂P, (0 : ℝ) ≤ 0 := by
    intro k
    filter_upwards [] with ω
    exact le_refl _
  have hLedger : ∀ k, ∀ᵐ ω ∂P,
      V ω - U ω ≤ K ω + E k ω + (0 : ℝ) := by
    intro k
    filter_upwards [hUpper k] with ω hω
    simpa using hω
  obtain ⟨e, r, heI, heSmall, hr, hBound⟩ :=
    avram_pj_reward79_two_stage_cutoff_mesh_signed_L1_budget
      P (fun ω => V ω - U ω) K E (fun _ _ => (0 : ℝ))
      (ε / 2) (by positivity)
      hKI (by convert hKsmall using 1 <;> ring)
      hEI hQ hLedger hVan
  have hPosEq :
      (fun ω => max (0 : ℝ) (G ω - U ω)) =
        (fun ω => ((G ω - U ω) + |G ω - U ω|) / 2) := by
    funext ω
    rcases le_total (G ω - U ω) 0 with h | h
    · rw [max_eq_left h, abs_of_nonpos h]
      ring
    · rw [max_eq_right h, abs_of_nonneg h]
      ring
  have hPosI :
      Integrable (fun ω => max (0 : ℝ) (G ω - U ω)) P := by
    rw [hPosEq]
    exact (hGapI.add hGapI.abs).div_const 2
  have hPosLe : ∀ᵐ ω ∂P,
      max (0 : ℝ) (G ω - U ω) ≤ |e ω| := by
    filter_upwards [hCompare, hr, hBound] with ω hc hrω hb
    have hVu : V ω - U ω ≤ e ω := by linarith
    have hVuPos : max (0 : ℝ) (V ω - U ω) ≤ |e ω| :=
      max_le (abs_nonneg _) (hVu.trans (le_abs_self _))
    exact max_le (abs_nonneg _) (hc.trans hVuPos)
  exact (integral_mono_ae hPosI heI.abs hPosLe).trans heSmall
