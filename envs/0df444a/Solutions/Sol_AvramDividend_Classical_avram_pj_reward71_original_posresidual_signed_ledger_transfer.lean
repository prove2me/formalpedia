-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward71_original_posresidual_signed_ledger_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:31:12.526571+00:00
-- url     : https://prove2.me/submissions/a5a91708-0dcb-4e26-bdd5-19175bb25aa8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (G U E R : Ω → ℝ) (ε : ℝ)
    (hGU : Integrable (fun ω => G ω - U ω) P)
    (hE : Integrable E P)
    (herror : ∀ᵐ ω ∂P, G ω - U ω ≤ E ω + R ω)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hEabs : (∫ ω, |E ω| ∂P) ≤ ε) :
    (∫ ω in A, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε := by
  have hPosI : Integrable (fun ω => max (0 : ℝ) (G ω - U ω)) P := by
    convert hGU.pos_part using 1
    funext ω
    simp [max_comm]
  have hNonneg :
      ∀ᵐ ω ∂P, 0 ≤ max (0 : ℝ) (G ω - U ω) :=
    Filter.Eventually.of_forall (fun ω => le_max_left _ _)
  have hDom :
      ∀ᵐ ω ∂P, max (0 : ℝ) (G ω - U ω) ≤ |E ω| := by
    filter_upwards [herror, hR] with ω hi hr
    apply max_le
    · exact abs_nonneg _
    · have hLe : G ω - U ω ≤ E ω := by linarith
      exact hLe.trans (le_abs_self _)
  have hGlobal :
      (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤
        (∫ ω, |E ω| ∂P) :=
    integral_mono_ae hPosI hE.abs hDom
  exact (setIntegral_le_integral hPosI hNonneg).trans (hGlobal.trans hEabs)
