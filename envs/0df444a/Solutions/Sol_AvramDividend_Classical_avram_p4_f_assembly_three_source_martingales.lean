-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_three_source_martingales
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:52:40.733927+00:00
-- url     : https://prove2.me/submissions/e0856f32-594a-4c91-83b5-161aa2bcbca2

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Assemble independently integrable centred continuous, compensated-small-jump,
    and large-jump martingale parts into the precise signed residual witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (x : ℝ)
    (Term Cash Mc Ms Ml G H : Ω → ℝ)
    (hc : Integrable Mc P) (hs : Integrable Ms P)
    (hl : Integrable Ml P) (hg : Integrable G P)
    (hh : Integrable H P)
    (hc0 : (∫ ω, Mc ω ∂P) = 0)
    (hs0 : (∫ ω, Ms ω ∂P) = 0)
    (hl0 : (∫ ω, Ml ω ∂P) = 0)
    (hres : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hito : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + H ω) :
    ∃ M G' H' : Ω → ℝ,
      Integrable M P ∧ Integrable G' P ∧ Integrable H' P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G' ω + H' ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + M ω + G' ω + H' ω) := by
  have hcs : Integrable (fun ω => Mc ω + Ms ω) P := hc.add hs
  have hm : Integrable (fun ω => Mc ω + Ms ω + Ml ω) P := hcs.add hl
  refine ⟨fun ω => Mc ω + Ms ω + Ml ω, G, H, hm, hg, hh, ?_, hres, ?_⟩
  · calc
      (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
          (∫ ω, Mc ω + Ms ω ∂P) + (∫ ω, Ml ω ∂P) :=
            integral_add hcs hl
      _ = (∫ ω, Mc ω ∂P) + (∫ ω, Ms ω ∂P) +
          (∫ ω, Ml ω ∂P) := by rw [integral_add hc hs]
      _ = 0 := by rw [hc0, hs0, hl0]; ring
  · filter_upwards [hito] with ω hω
    simpa only [add_assoc] using hω
