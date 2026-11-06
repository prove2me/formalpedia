-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_ae_natural_clock_fatou_L1_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:00:01.913177+00:00
-- url     : https://prove2.me/submissions/a45a65f1-f55c-493a-bd71-621a57d8113d

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal Topology
noncomputable section

/-- Fatou with almost-sure convergence, appropriate for genuine stochastic
spatial localisers whose cofinality holds away from an exceptional null set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (F : ℕ → Ω → ℝ)
    (hSmeas : AEStronglyMeasurable S P)
    (hSnonneg : 0 ≤ᵐ[P] S)
    (hFmeas : ∀ k, Measurable (F k))
    (hFint : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hlim : ∀ᵐ ω ∂P, Tendsto
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
  have hLin : (∫⁻ ω, ENNReal.ofReal (S ω) ∂P) ≤ ENNReal.ofReal b := by
    calc
      (∫⁻ ω, ENNReal.ofReal (S ω) ∂P) =
        (∫⁻ ω, Filter.liminf (fun k => ENNReal.ofReal (F k ω)) atTop ∂P) := by
          apply lintegral_congr_ae
          filter_upwards [hlim] with ω h
          exact (h.liminf_eq).symm
      _ ≤ Filter.liminf (fun k => ∫⁻ ω, ENNReal.ofReal (F k ω) ∂P)
          atTop := lintegral_liminf_le hFn
      _ ≤ ENNReal.ofReal b := by
          apply Filter.liminf_le_of_le
          · change Filter.IsBoundedUnder (fun x y : ℝ≥0∞ => x ≥ y)
              atTop (fun k => ∫⁻ ω, ENNReal.ofReal (F k ω) ∂P)
            exact ⟨0, Filter.Eventually.of_forall (fun k => bot_le)⟩
          · intro c hc
            obtain ⟨j, hcj, hbj⟩ :=
              (hc.and (Filter.Eventually.of_forall hB)).exists
            exact hcj.trans hbj
  have hFin : (∫⁻ ω, ENNReal.ofReal (S ω) ∂P) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hLin ENNReal.ofReal_lt_top)
  have hSI : Integrable S P :=
    (lintegral_ofReal_ne_top_iff_integrable hSmeas hSnonneg).mp hFin
  refine ⟨hSI, ?_⟩
  have hEq : ENNReal.ofReal (∫ ω, S ω ∂P) =
      (∫⁻ ω, ENNReal.ofReal (S ω) ∂P) :=
    ofReal_integral_eq_lintegral_ofReal hSI hSnonneg
  exact (ENNReal.ofReal_le_ofReal_iff hb).mp (hEq.trans_le hLin)
