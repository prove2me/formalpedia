-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:43:44.730557+00:00
-- url     : https://prove2.me/submissions/528dc766-7f39-4299-be7a-7dc26bf67c22

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_nonnegative_physical_residual_auto_L1_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical

noncomputable section

/-- Three actual local stopped martingale terms and signed Itô remainders
imply both L1 and the HJB payoff bound, without an L1 condition on G or R. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F Mc Ms Ml G R : Ω → ℝ) (b : ℝ)
    (hFmeas : AEStronglyMeasurable F P)
    (hFnonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hMcI : Integrable Mc P) (hMsI : Integrable Ms P)
    (hMlI : Integrable Ml P)
    (hMc0 : (∫ ω, Mc ω ∂P) = 0)
    (hMs0 : (∫ ω, Ms ω ∂P) = 0)
    (hMl0 : (∫ ω, Ml ω ∂P) = 0)
    (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      F ω ≤ b + Mc ω + Ms ω + Ml ω + G ω + R ω) :
    Integrable F P ∧ (∫ ω, F ω ∂P) ≤ b := by
  let M : Ω → ℝ := fun ω => Mc ω + (Ms ω + Ml ω)
  have hMI : Integrable M P := hMcI.add (hMsI.add hMlI)
  have hMZero : (∫ ω, M ω ∂P) = 0 := by
    change (∫ ω, (Mc + (Ms + Ml)) ω ∂P) = 0
    calc
      _ = (∫ ω, Mc ω ∂P) + (∫ ω, (Ms + Ml) ω ∂P) :=
        integral_add hMcI (hMsI.add hMlI)
      _ = (∫ ω, Mc ω ∂P) +
            ((∫ ω, Ms ω ∂P) + (∫ ω, Ml ω ∂P)) := by
        congr 1
        exact integral_add hMsI hMlI
      _ = 0 := by simp [hMc0, hMs0, hMl0]
  have hUpper : ∀ᵐ ω ∂P, F ω ≤ b + M ω := by
    filter_upwards [hIto, hG, hR] with ω hpath hg hr
    dsimp [M]
    linarith only [hpath, hg, hr]
  exact avram_ubv_loc6_nonnegative_physical_residual_auto_L1_budget
    F M b hFmeas hFnonneg hMI hUpper (le_of_eq hMZero)
