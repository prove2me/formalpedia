-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_approximate_mean_zero_budget_implies_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:35:08.120121+00:00
-- url     : https://prove2.me/submissions/b61a59b3-2274-4470-99dd-50000a4d248f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Uniformly vanishing signed L1 errors transfer an original stopped finite-cap
Ito estimate into the required expected upper bound at every stopping subclock. -/
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
    (σ : ℕ → Ω → ℝ≥0) (hσle : ∀ k ω, σ k ω ≤ τ ω)
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
    (hApprox : ∀ k, ∃ M Err : ℕ → Ω → ℝ,
      (∀ j, Integrable (M j) P ∧ (∫ ω, M j ω ∂P) = 0) ∧
      (∀ j, Integrable (Err j) P) ∧
      Tendsto (fun j => ∫ ω, Err j ω ∂P) atTop (nhds (0 : ℝ)) ∧
      (∀ j, ∀ᵐ ω ∂P,
        F k ω ≤ w x + M j ω + Err j ω)) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨M, Err, hM, hErrI, hErrLim, hBound⟩ := hApprox k
  have hConst : Integrable (fun _ : Ω => w x) P := integrable_const (w x)
  have hEach : ∀ j, (∫ ω, F k ω ∂P) ≤
      w x + (∫ ω, Err j ω ∂P) := by
    intro j
    obtain ⟨hMI, hM0⟩ := hM j
    have hCadd : Integrable (fun ω => w x + M j ω) P :=
      hConst.add hMI
    have hAll : Integrable (fun ω => w x + M j ω + Err j ω) P :=
      hCadd.add (hErrI j)
    have hMono : (∫ ω, F k ω ∂P) ≤
        (∫ ω, w x + M j ω + Err j ω ∂P) :=
      integral_mono_ae (hFI k) hAll (hBound j)
    have hEval : (∫ ω, w x + M j ω + Err j ω ∂P) =
        w x + (∫ ω, Err j ω ∂P) := by
      rw [integral_add hCadd (hErrI j)]
      rw [integral_add hConst hMI]
      simp [hM0]
    exact hMono.trans_eq hEval
  have hLimit : Tendsto (fun j => w x + (∫ ω, Err j ω ∂P))
      atTop (nhds (w x)) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => w x)
        atTop (nhds (w x))).add hErrLim)
  exact ge_of_tendsto hLimit (Filter.Eventually.of_forall hEach)
