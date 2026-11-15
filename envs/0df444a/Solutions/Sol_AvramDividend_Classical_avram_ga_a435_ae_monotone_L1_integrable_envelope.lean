-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a435_ae_monotone_L1_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:06:23.472728+00:00
-- url     : https://prove2.me/submissions/b8d6b6e3-0b6a-4a9c-90ed-1bbe0bf8cdc5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hint : ∀ k, Integrable (f k) P)
    (hnonneg : ∀ k ω, 0 ≤ f k ω)
    (hmono : ∀ ω, Monotone (fun k => f k ω))
    (hbudget : ∀ k, (∫ ω, f k ω ∂P) ≤ K) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      ∀ᵐ ω ∂P, 0 ≤ S ω ∧ ∀ k, f k ω ≤ S ω := by
  classical
  let F : Ω → ℝ≥0∞ := fun ω => ⨆ k, ENNReal.ofReal (f k ω)
  have hae (k : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal (f k ω)) P :=
    (hint k).aemeasurable.ennreal_ofReal
  have hFm : AEMeasurable F P :=
    AEMeasurable.iSup hae
  have hmonoF (ω : Ω) : Monotone (fun k => ENNReal.ofReal (f k ω)) := by
    intro i j hij
    exact ENNReal.ofReal_le_ofReal (hmono ω hij)
  have hboundF : (∫⁻ ω, F ω ∂P) ≤ ENNReal.ofReal K := by
    rw [show (∫⁻ ω, F ω ∂P) =
      ⨆ k, ∫⁻ ω, ENNReal.ofReal (f k ω) ∂P from
        lintegral_iSup' hae
          (Filter.Eventually.of_forall fun ω => hmonoF ω)]
    refine iSup_le fun k => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
      (Filter.Eventually.of_forall (hnonneg k))]
    exact ENNReal.ofReal_le_ofReal (hbudget k)
  have hFfinite : (∫⁻ ω, F ω ∂P) < ⊤ :=
    lt_of_le_of_lt hboundF ENNReal.ofReal_lt_top
  have hFae : ∀ᵐ ω ∂P, F ω < ⊤ :=
    ae_lt_top' hFm (ne_top_of_lt hFfinite)
  let S : Ω → ℝ := fun ω => (F ω).toReal
  have hSm : AEStronglyMeasurable S P :=
    hFm.ennreal_toReal.aestronglyMeasurable
  have hSfinite : HasFiniteIntegral S P := by
    change (∫⁻ ω, ‖S ω‖ₑ ∂P) < ⊤
    calc
      (∫⁻ ω, ‖S ω‖ₑ ∂P) ≤ ∫⁻ ω, F ω ∂P := by
        apply lintegral_mono
        intro ω
        change ‖(F ω).toReal‖ₑ ≤ F ω
        rw [Real.enorm_eq_ofReal (ENNReal.toReal_nonneg)]
        exact ENNReal.ofReal_toReal_le
      _ < ⊤ := hFfinite
  refine ⟨S, ⟨hSm,hSfinite⟩, ?_⟩
  filter_upwards [hFae] with ω hω
  constructor
  · exact ENNReal.toReal_nonneg
  · intro k
    have hle : ENNReal.ofReal (f k ω) ≤ F ω := by
      change ENNReal.ofReal (f k ω) ≤ ⨆ j, ENNReal.ofReal (f j ω)
      exact le_iSup (fun j => ENNReal.ofReal (f j ω)) k
    have hle' := ENNReal.toReal_mono (ne_top_of_lt hω) hle
    simpa [S, ENNReal.toReal_ofReal (hnonneg k ω)] using hle' 
