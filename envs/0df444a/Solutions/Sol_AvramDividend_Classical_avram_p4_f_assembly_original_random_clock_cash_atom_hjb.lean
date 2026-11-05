-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_random_clock_cash_atom_hjb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:48:10.032347+00:00
-- url     : https://prove2.me/submissions/d1105f83-688a-492b-a9ef-6e12995afa3c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Literal random-clock Cash splits into paid atoms and diffuse cash with atomic HJB control. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      let E : Set ℝ := {t | t ∈ A ∧
        t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
      A.Countable ∧
      Cash ω =
        (∑' a : E,
          (ENNReal.ofReal (Real.exp (-(q * a.1))) *
            μatom {a.1}).toReal) +
        (∫⁻ s : ℝ,
          (if s ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * s))) else 0)
            ∂μdiffuse).toReal ∧
      (∑' a : E,
        ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}) ≤
      ∑' a : E,
        ENNReal.ofReal (Real.exp (-(q * a.1))) *
          ENNReal.ofReal
            (w (riskProcess X x D (Real.toNNReal a.1) ω) -
              w (riskProcess X x D (Real.toNNReal a.1) ω -
                (rightLimit D (Real.toNNReal a.1) ω -
                  D (Real.toNNReal a.1) ω))) := by
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hNull, hAc, hDiffuse,
    hRight, hSummable, hCashEq⟩ :=
    avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
      X x D hD q hq ω (τ ω)
  refine ⟨A, μatom, μdiffuse, ?_⟩
  dsimp only
  let E : Set ℝ := {t | t ∈ A ∧
    t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
  constructor
  · exact hCount
  constructor
  · rw [hCash ω]
    let e : {a : A // a.1 ∈ paymentTimes (ruinTime X x D ω) ∧
        μatom {a.1} ≠ 0} ≃ E :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun t => t ∈ A)
        (fun t => t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0)
    rw [← e.tsum_eq (fun a : E =>
      (ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}).toReal)]
    exact hCashEq
  have hPhysical :=
    avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
      X x D w hjump ω (τ ω) A μatom μdiffuse hSplit hRight
  have hMass : ∀ a : E,
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω) := by
    intro a
    rcases hPhysical a with ⟨_, _, _, _, hAtomMass, _⟩
    exact hAtomMass
  have hPaid : ∀ a : E,
      Real.toNNReal a.1 = 0 ∨
        (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω := by
    intro a
    rcases hPhysical a with ⟨_, _, hEligibility, _, _, _⟩
    exact hEligibility
  exact avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
    X x D w q hjump ω E μatom hMass hPaid
