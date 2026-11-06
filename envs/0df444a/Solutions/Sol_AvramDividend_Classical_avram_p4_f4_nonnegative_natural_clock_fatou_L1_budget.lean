-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_nonnegative_natural_clock_fatou_L1_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:04:50.852192+00:00
-- url     : https://prove2.me/submissions/1a5042e8-bd5a-4644-a942-e2647b2d01e5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_one_sided_lintegral_le_of_grid_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section

/-- A physical nonnegative stopped-payoff Fatou upper bound makes the
natural-clock reward integrable and preserves its real expectation budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (F : ℕ → Ω → ℝ)
    (hSmeas : AEStronglyMeasurable S P)
    (hSnonneg : 0 ≤ᵐ[P] S)
    (hFmeas : ∀ k, Measurable (F k))
    (hFint : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hlim : ∀ ω, Tendsto
      (fun k => ENNReal.ofReal (F k ω)) atTop
      (𝓝 (ENNReal.ofReal (S ω))))
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ k, (∫ ω, F k ω ∂P) ≤ b) :
    Integrable S P ∧ (∫ ω, S ω ∂P) ≤ b := by
  have hFn : ∀ k, Measurable (fun ω => ENNReal.ofReal (F k ω)) :=
    fun k => (hFmeas k).ennreal_ofReal
  have hB : ∀ k, (∫⁻ ω, ENNReal.ofReal (F k ω) ∂P) ≤
      ENNReal.ofReal b := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint k) (hFnonneg k)]
    exact (ENNReal.ofReal_le_ofReal_iff hb).mpr (hBudget k)
  have hLin : (∫⁻ ω, ENNReal.ofReal (S ω) ∂P) ≤ ENNReal.ofReal b :=
    one_sided_lintegral_le_of_grid_tendsto
      P (fun k ω => ENNReal.ofReal (F k ω))
      (fun ω => ENNReal.ofReal (S ω)) hFn hlim
      (ENNReal.ofReal b) hB
  have hFin : (∫⁻ ω, ENNReal.ofReal (S ω) ∂P) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hLin ENNReal.ofReal_lt_top)
  have hSI : Integrable S P :=
    (lintegral_ofReal_ne_top_iff_integrable hSmeas hSnonneg).mp hFin
  refine ⟨hSI, ?_⟩
  have hEq : ENNReal.ofReal (∫ ω, S ω ∂P) =
      (∫⁻ ω, ENNReal.ofReal (S ω) ∂P) :=
    ofReal_integral_eq_lintegral_ofReal hSI hSnonneg
  exact (ENNReal.ofReal_le_ofReal_iff hb).mp (hEq.trans_le hLin)