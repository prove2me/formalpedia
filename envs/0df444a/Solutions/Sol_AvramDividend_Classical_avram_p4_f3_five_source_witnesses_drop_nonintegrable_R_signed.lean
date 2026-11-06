-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_five_source_witnesses_drop_nonintegrable_R_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:59:25.562367+00:00
-- url     : https://prove2.me/submissions/734bc7bf-17d2-4f75-a88e-1bdbabb8ba6b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical

/-- Source five-witness reduction without any integrability assumption on R. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Term Cash : Ω → ℝ) (b : ℝ)
    (hSource : ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        b + Mc ω + Ms ω + Ml ω + G ω + R ω)) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ b + M ω + G ω + H ω) := by
  rcases hSource with ⟨Mc, Ms, Ml, G, R,
    hMcI, hMsI, hMlI, hGI, hMc0, hMs0, hMl0,
    hGnonpos, hRnonpos, hBudget⟩
  have hz : Integrable (fun _ : Ω => (0 : ℝ)) P :=
    integrable_zero Ω ℝ P
  have hsign : ∀ᵐ ω ∂P, (0 : ℝ) + 0 ≤ 0 :=
    Filter.Eventually.of_forall (fun _ => by norm_num)
  have hupper : ∀ᵐ ω ∂P, Term ω + Cash ω ≤
      (fun _ : ℝ => b) 0 + Mc ω + Ms ω + Ml ω + (0 : ℝ) + 0 := by
    filter_upwards [hBudget, hGnonpos, hRnonpos] with ω hb hg hr
    linarith
  exact avram_p4_f_assembly_three_source_martingales
    (fun _ : ℝ => b) 0 Term Cash Mc Ms Ml (fun _ => 0) (fun _ => 0)
    hMcI hMsI hMlI hz hz hMc0 hMs0 hMl0 hsign hupper
