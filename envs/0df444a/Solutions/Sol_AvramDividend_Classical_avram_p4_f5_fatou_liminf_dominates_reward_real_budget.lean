-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f5_fatou_liminf_dominates_reward_real_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:05:47.547345+00:00
-- url     : https://prove2.me/submissions/15cb10a2-de9b-443e-bd4c-bc2bae32314f

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal Topology
noncomputable section

/-- The natural reward may lie below local liminf at a downward ruin jump;
Fatou still bounds its expectation without terminal L1 convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (F : ℕ → Ω → ℝ)
    (hSmeas : AEStronglyMeasurable S P)
    (hSnonneg : 0 ≤ᵐ[P] S)
    (hFmeas : ∀ k, Measurable (F k))
    (hFint : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hliminf : ∀ᵐ ω ∂P,
      ENNReal.ofReal (S ω) ≤
        Filter.liminf (fun k => ENNReal.ofReal (F k ω)) atTop)
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
      (∫⁻ ω, ENNReal.ofReal (S ω) ∂P) ≤
        (∫⁻ ω, Filter.liminf (fun k => ENNReal.ofReal (F k ω)) atTop ∂P) :=
          lintegral_mono_ae hliminf
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
