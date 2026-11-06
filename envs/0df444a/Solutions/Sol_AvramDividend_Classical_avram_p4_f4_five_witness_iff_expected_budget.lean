-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_five_witness_iff_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:10:29.120202+00:00
-- url     : https://prove2.me/submissions/efcb3f22-df8f-4d87-bc24-e9a282825512

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

noncomputable section

/-- The five residual slots at an original stopped clock are equivalent
to its expected payoff budget once terminal and cash integrability hold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Term Cash : Ω → ℝ) (hTerm : Integrable Term P)
    (hCash : Integrable Cash P) (b : ℝ) :
    (∫ ω, Term ω + Cash ω ∂P) ≤ b ↔
      ∃ Mc Ms Ml G R : Ω → ℝ,
        Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
        Integrable G P ∧
        (∫ ω, Mc ω ∂P) = 0 ∧
        (∫ ω, Ms ω ∂P) = 0 ∧
        (∫ ω, Ml ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, G ω ≤ 0) ∧
        (∀ᵐ ω ∂P, R ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Term ω + Cash ω ≤
          b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  have hZ : Integrable (fun ω => Term ω + Cash ω) P := hTerm.add hCash
  constructor
  · intro hBudget
    let a : ℝ := ∫ ω, Term ω + Cash ω ∂P
    refine ⟨(fun ω => Term ω + Cash ω - a), (fun _ => 0), (fun _ => 0),
      (fun _ => a - b), (fun _ => 0),
      hZ.sub (integrable_const _), integrable_zero _ _ _,
      integrable_zero _ _ _, integrable_const _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hMean : (∫ ω, Term ω + Cash ω - a ∂P) =
          (∫ ω, Term ω + Cash ω ∂P) - a := by
        rw [integral_sub hZ (integrable_const _)]
        simp
      simp only [a] at hMean
      linarith
    · simp
    · simp
    · filter_upwards [] with ω
      change a - b ≤ 0
      exact sub_nonpos.mpr hBudget
    · filter_upwards [] with ω
      norm_num
    · filter_upwards [] with ω
      change Term ω + Cash ω ≤ b + (Term ω + Cash ω - a) +
        0 + 0 + (a - b) + 0
      ring_nf
      exact le_refl _
  · rintro ⟨Mc, Ms, Ml, G, R, hMc, hMs, hMl, hG, hMc0,
      hMs0, hMl0, hGneg, hRneg, hPath⟩
    have hUpper : Integrable (fun ω => b + Mc ω + Ms ω + Ml ω) P :=
      (((integrable_const _).add hMc).add hMs).add hMl
    have hAE : ∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ b + Mc ω + Ms ω + Ml ω := by
      filter_upwards [hGneg, hRneg, hPath] with ω hg hr hp
      linarith
    have hInt := integral_mono_ae hZ hUpper hAE
    have hI1 : Integrable (fun ω => b + Mc ω) P :=
      (integrable_const _).add hMc
    have hI2 : Integrable (fun ω => b + Mc ω + Ms ω) P :=
      hI1.add hMs
    have hIntUpper :
        (∫ ω, b + Mc ω + Ms ω + Ml ω ∂P) = b := by
      rw [integral_add hI2 hMl]
      rw [integral_add hI1 hMs]
      rw [integral_add (integrable_const _) hMc]
      simp only [hMc0, hMs0, hMl0, add_zero]
      simp
    linarith