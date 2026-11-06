-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_stopped_terminal_L1_of_combined_ennreal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:23:56.797994+00:00
-- url     : https://prove2.me/submissions/914bf37c-759e-4c93-8803-bbe05066146f

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A finite nonnegative combined stopped-payoff ENNReal budget
establishes genuine terminal L1, including at an unbounded reserve cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Term Cash : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : 0 ≤ᵐ[P] Term)
    (hCashI : Integrable Cash P)
    (hCashNonneg : 0 ≤ᵐ[P] Cash)
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget :
      (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
        ENNReal.ofReal b) :
    Integrable Term P ∧ (∫ ω, Term ω + Cash ω ∂P) ≤ b := by
  have hSMeas : AEStronglyMeasurable
      (fun ω => Term ω + Cash ω) P :=
    hTermMeas.add hCashI.aestronglyMeasurable
  have hSNonneg : 0 ≤ᵐ[P] (fun ω => Term ω + Cash ω) := by
    filter_upwards [hTermNonneg, hCashNonneg] with ω ht hc
    exact add_nonneg ht hc
  have hSFinite :
      (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hBudget ENNReal.ofReal_lt_top)
  have hSI : Integrable (fun ω => Term ω + Cash ω) P :=
    (lintegral_ofReal_ne_top_iff_integrable hSMeas hSNonneg).mp hSFinite
  have hTermI : Integrable Term P := by
    have hFun : (fun ω => Term ω + Cash ω) - Cash = Term := by
      funext ω
      change Term ω + Cash ω - Cash ω = Term ω
      ring
    simpa only [hFun] using (hSI.sub hCashI)
  refine ⟨hTermI, ?_⟩
  have hEq :
      ENNReal.ofReal (∫ ω, Term ω + Cash ω ∂P) =
        (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) :=
    ofReal_integral_eq_lintegral_ofReal hSI hSNonneg
  exact (ENNReal.ofReal_le_ofReal_iff hb).mp (hEq.trans_le hBudget)
