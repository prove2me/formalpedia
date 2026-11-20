-- Prove2me | solution 3 for AvramDividend.Classical.avram_jump6_E_original_canonical_positive_at_ruin_payment_contact_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:01:21.881138+00:00
-- url     : https://prove2.me/submissions/f92f06b0-b797-4cde-b916-ab809c70f689
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_topcap_actual_ruincontact_cash_grid_limit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_ruincontact_finite_mesh_signed_cash_finitecap
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_ruincontact_mesh_discount_and_true_cash_tail_tends_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k : ℕ,
      let Cash : Ω → ℝ := fun ω : Ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      let u : ℕ → ℕ → ℝ≥0 := fun j i =>
        (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
      let Source : ℕ → Ω → ℝ := fun n ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (m n),
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
      let Dividend : ℕ → Ω → ℝ := fun n ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
      (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (m n),
          ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
            E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
            E (v (i + 1)) *
              (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            E (v (i + 1)) *
              (w (Y (v (i + 1))) -
                w (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (σ k ω) *
          (w (riskProcess X x D (σ k ω) ω) - w (Y (σ k ω)))) -
        Source n ω
      ∀ᵐ ω ∂P, (0 < σ k ω ∧ (σ k ω : ℝ≥0∞) = ruinTime X x D ω) →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in atTop, Dividend n ω + Cash ω ≤ ε := by
  by_cases hTop : C = ⊤
  · intro k Cash u m Source Dividend
    have hbase := avram_jump6_B_topcap_actual_ruincontact_cash_grid_limit
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτstop σ F hσstop hσle hFsource hFI hInfiniteActivity hTop k
    filter_upwards [hbase] with ω hω
    intro hcase ε hε
    exact hω ⟨ne_of_gt hcase.1, hcase.2⟩ ε hε
  · intro k
    have hmesh :=
      avram_jump6_B_original_ruincontact_finite_mesh_signed_cash_finitecap
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
        τ hτeq hτstop σ F hσstop hσle hFsource hFI hInfiniteActivity hTop k
    filter_upwards [hmesh] with ω hboundω
    intro hcase ε hε; obtain ⟨hσpos, hcontact⟩ := hcase
    have htail :=
      avram_jump6_B_ruincontact_mesh_discount_and_true_cash_tail_tends_zero
        X x D hD.1.1 ω (σ k ω) q (le_of_lt hq) n hn
    filter_upwards [htail.eventually (Iio_mem_nhds hε)] with j hj
    have hb := hboundω ⟨hσpos, hcontact⟩ j
    have hpre : ¬(σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω) := by
      simp [ne_of_gt hσpos, hcontact]
    dsimp at *; simp only [if_neg hpre, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] at *
    nlinarith
