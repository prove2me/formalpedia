-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_masked_expected_to_signed_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:28:39.893203+00:00
-- url     : https://prove2.me/submissions/0b9f4813-7383-49b2-a34a-bb7c93bd62ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A source-exact masked expected bound yields integrable centred witnesses
for the original finite-cap stopped payoff, without asserting an Ito source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hMaskedUpper : ∀ k,
      (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P) ≤ w x) :
    ∀ k, ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else F k ω) ≤
          w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  let T : Ω → ℝ := fun ω => if σ k ω = 0 then w x else F k ω
  have hTI : Integrable T P := by
    exact avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
      (σ k) (hσstop k) (F k) (hFI k) (w x)
  have hTupper : (∫ ω, T ω ∂P) ≤ w x := hMaskedUpper k
  let M : Ω → ℝ := fun ω => T ω - (∫ η, T η ∂P)
  have hMI : Integrable M P :=
    hTI.sub (integrable_const _)
  have hMzero : (∫ ω, M ω ∂P) = 0 := by
    calc
      (∫ ω, M ω ∂P) =
          (∫ ω, T ω ∂P) - (∫ _ : Ω, (∫ η, T η ∂P) ∂P) := by
            simpa only [M, Pi.sub_apply] using
              (integral_sub hTI (integrable_const (∫ η, T η ∂P)))
      _ = 0 := by simp
  refine ⟨M, (fun _ => 0), (fun _ => 0), (fun _ => 0), (fun _ => 0),
    hMI, integrable_const _, integrable_const _, hMzero, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Filter.Eventually.of_forall (fun ω => le_rfl)
  · exact Filter.Eventually.of_forall (fun ω => le_rfl)
  · apply Filter.Eventually.of_forall
    intro ω
    change T ω ≤ w x + M ω + 0 + 0 + 0 + 0
    dsimp [M]
    linarith
