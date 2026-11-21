-- Prove2me | solution 1 for BFWFluidLimit.conditionalIndependence_repairs_moments
-- status  : ACCEPTED   (prove)
-- author  : @wfe2017
-- created : 2026-11-20T11:13:52.925646+00:00
-- url     : https://prove2.me/submissions/2891a5b1-9ac9-4143-90a2-6e50c5a5fb1e

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Constructions.Pi
set_option autoImplicit false

/-!
Current-price exogeneity for the corrected BFW Theorem 3.1.
This file uses only public Mathlib.  It proves the conditional moment consequences of the
explicit conditional-mean restriction; it does not assume that observations are IID.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace BFWFluidLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The information available after posting the entire current price vector. -/
abbrev withCurrentPrices {N : ℕ} (F : MeasurableSpace Ω) (P : Ω → Fin N → ℝ) :
    MeasurableSpace Ω :=
  F ⊔ MeasurableSpace.comap P inferInstance

/-- The additional exogeneity restriction needed during exploration.
The integrability clause rules out the default value of a nonintegrable conditional expectation.
-/
def CurrentPriceExogenous {N : ℕ} (μ : Measure Ω) (F : MeasurableSpace Ω)
    (P : Ω → Fin N → ℝ) (ε : Ω → ℝ) : Prop :=
  Integrable ε μ ∧ μ[ε | withCurrentPrices F P] =ᵐ[μ] 0

/-- Conditional mean independence is sufficient.  This is weaker than conditional independence
of the whole noise distribution and does not assert IID noise. -/
theorem currentPriceExogenous_of_conditionalMeanIndependence {N : ℕ}
    {μ : Measure Ω} {F : MeasurableSpace Ω} {P : Ω → Fin N → ℝ} {ε : Ω → ℝ}
    (hε : Integrable ε μ)
    (hind : μ[ε | withCurrentPrices F P] =ᵐ[μ] μ[ε | F])
    (hzero : μ[ε | F] =ᵐ[μ] 0) : CurrentPriceExogenous (mΩ := mΩ) μ F P ε :=
  ⟨hε, hind.trans hzero⟩

/-- Conditional independence expressed by conditional expectations of all integrable
measurable functions of the full noise vector.  This explicit characterization works on an
arbitrary measurable probability space; no `StandardBorelSpace Ω` instance is required.
Its equivalence to Mathlib's kernel-based `CondIndepFun` is not claimed in this file. -/
def NoisePriceConditionallyIndependent {N : ℕ} (μ : Measure Ω)
    (F : MeasurableSpace Ω) (P E : Ω → Fin N → ℝ) : Prop :=
  ∀ φ : (Fin N → ℝ) → ℝ, Measurable φ → Integrable (φ ∘ E) μ →
    μ[φ ∘ E | withCurrentPrices F P] =ᵐ[μ] μ[φ ∘ E | F]

/-- The explicit full-noise conditional independence assumption, together with the printed
martingale-difference condition, supplies each coordinate of current-price exogeneity. -/
theorem NoisePriceConditionallyIndependent.coordinate_exogenous {N : ℕ}
    {μ : Measure Ω} {F : MeasurableSpace Ω} {P E : Ω → Fin N → ℝ}
    (hind : NoisePriceConditionallyIndependent (mΩ := mΩ) μ F P E) (i : Fin N)
    (hε : Integrable (fun ω => E ω i) μ)
    (hzero : μ[(fun ω => E ω i) | F] =ᵐ[μ] 0) :
    CurrentPriceExogenous (mΩ := mΩ) μ F P (fun ω => E ω i) := by
  apply currentPriceExogenous_of_conditionalMeanIndependence (mΩ := mΩ) hε _ hzero
  exact hind (fun x => x i) (measurable_pi_apply i) hε

/-- Enlarged-information exogeneity implies the paper's past-information mean-zero restriction. -/
theorem CurrentPriceExogenous.past_mean_zero {N : ℕ} {μ : Measure Ω}
    [IsFiniteMeasure μ] {F : MeasurableSpace Ω} {P : Ω → Fin N → ℝ} {ε : Ω → ℝ}
    (hG : withCurrentPrices F P ≤ mΩ) (hε : CurrentPriceExogenous (mΩ := mΩ) μ F P ε) :
    μ[ε | F] =ᵐ[μ] 0 := by
  let : IsFiniteMeasure (μ.trim hG) := MeasureTheory.isFiniteMeasure_trim hG
  have ht := condExp_condExp_of_le (m₁ := F) (m₂ := withCurrentPrices F P) (m₀ := mΩ) (μ := μ) (f := ε)
    (le_sup_left : F ≤ withCurrentPrices F P) hG
  exact ht.symm.trans ((condExp_congr_ae hε.2).trans (by simp))

/-- Every bounded measurable current-price multiplier is conditionally orthogonal to noise. -/
theorem CurrentPriceExogenous.weighted_mean_zero {N : ℕ} {μ : Measure Ω}
    [IsFiniteMeasure μ] {F : MeasurableSpace Ω} {P : Ω → Fin N → ℝ} {ε w : Ω → ℝ}
    (hG : withCurrentPrices F P ≤ mΩ) (hε : CurrentPriceExogenous (mΩ := mΩ) μ F P ε)
    (hw : StronglyMeasurable[withCurrentPrices F P] w)
    (C : ℝ) (hC : ∀ᵐ ω ∂μ, ‖w ω‖ ≤ C) :
    μ[(fun ω => w ω * ε ω) | F] =ᵐ[μ] 0 := by
  have hpull := condExp_stronglyMeasurable_mul_of_bound hG hw hε.1 C hC
  have hweighted : μ[(fun ω => w ω * ε ω) | withCurrentPrices F P] =ᵐ[μ] 0 := by
    refine hpull.trans ?_
    filter_upwards [hε.2] with ω hω
    simp only [Pi.mul_apply, Pi.zero_apply] at *
    rw [hω, mul_zero]
  let : IsFiniteMeasure (μ.trim hG) := MeasureTheory.isFiniteMeasure_trim hG
  have ht := condExp_condExp_of_le (m₁ := F) (m₂ := withCurrentPrices F P) (m₀ := mΩ) (μ := μ) (f := fun ω => w ω * ε ω)
    (le_sup_left : F ≤ withCurrentPrices F P) hG
  exact ht.symm.trans ((condExp_congr_ae hweighted).trans (by simp))

/-- In particular, price times noise is a martingale difference. -/
theorem CurrentPriceExogenous.price_mul_mean_zero {N : ℕ} {μ : Measure Ω}
    [IsFiniteMeasure μ] {F : MeasurableSpace Ω} {P : Ω → Fin N → ℝ} {ε : Ω → ℝ}
    (hG : withCurrentPrices F P ≤ mΩ) (hε : CurrentPriceExogenous (mΩ := mΩ) μ F P ε)
    (i : Fin N) (C : ℝ) (hC : ∀ᵐ ω ∂μ, ‖P ω i‖ ≤ C) :
    μ[(fun ω => P ω i * ε ω) | F] =ᵐ[μ] 0 := by
  have hP : Measurable[withCurrentPrices F P] P :=
    (comap_measurable P).mono (le_sup_right :
      MeasurableSpace.comap P inferInstance ≤ withCurrentPrices F P) le_rfl
  exact CurrentPriceExogenous.weighted_mean_zero (mΩ := mΩ) hG hε ((measurable_pi_apply i).comp hP).stronglyMeasurable C hC

/-- The weighted innovation is integrable, using only bounded prices and integrable noise. -/
theorem CurrentPriceExogenous.integrable_price_mul {N : ℕ} {μ : Measure Ω}
    {F : MeasurableSpace Ω} {P : Ω → Fin N → ℝ} {ε : Ω → ℝ}
    (hP : Measurable[mΩ] P) (hε : CurrentPriceExogenous (mΩ := mΩ) μ F P ε)
    (i : Fin N) (C : ℝ) (hC : ∀ᵐ ω ∂μ, ‖P ω i‖ ≤ C) :
    Integrable (fun ω => P ω i * ε ω) μ :=
  hε.1.bdd_mul (((measurable_pi_apply i).comp hP).aestronglyMeasurable) hC

omit mΩ in
/-- If current prices are already history-measurable, the added restriction is automatic. -/
theorem withCurrentPrices_eq_of_measurable {N : ℕ} {F : MeasurableSpace Ω}
    {P : Ω → Fin N → ℝ} (hP : Measurable[F] P) : withCurrentPrices F P = F := by
  exact sup_eq_left.mpr hP.comap_le

/-- In exploitation, predictable prices need no additional independence hypothesis. -/
theorem currentPriceExogenous_of_predictable {N : ℕ} {μ : Measure Ω}
    {F : MeasurableSpace Ω} {P : Ω → Fin N → ℝ} {ε : Ω → ℝ}
    (hP : Measurable[F] P) (hε : Integrable ε μ) (hzero : μ[ε | F] =ᵐ[μ] 0) :
    CurrentPriceExogenous (mΩ := mΩ) μ F P ε := by
  exact ⟨hε, by simpa [withCurrentPrices_eq_of_measurable hP] using hzero⟩

/-- A noise term determined by current prices must vanish under the corrected exogeneity
assumption.  This explains why the displayed price-dependent counterexample is excluded. -/
theorem CurrentPriceExogenous.eq_zero_of_current_measurable {N : ℕ} {μ : Measure Ω}
    [IsFiniteMeasure μ] {F : MeasurableSpace Ω} {P : Ω → Fin N → ℝ} {ε : Ω → ℝ}
    (hG : withCurrentPrices F P ≤ mΩ)
    (hε : CurrentPriceExogenous (mΩ := mΩ) μ F P ε)
    (hm : StronglyMeasurable[withCurrentPrices F P] ε) : ε =ᵐ[μ] 0 := by
  simpa only [condExp_of_stronglyMeasurable hG hm hε.1] using hε.2

/-- Bounded price multipliers preserve the printed past-conditioned second-moment bound.
No second-moment bound conditional on the enlarged current-price information is assumed. -/
theorem bounded_mul_conditional_second_moment {μ : Measure Ω}
    {F : MeasurableSpace Ω} {ε w : Ω → ℝ} {C σ2 : ℝ}
    (hε2 : Integrable (fun ω => ε ω ^ 2) μ)
    (hw : AEStronglyMeasurable[mΩ] w μ) (hC0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂μ, ‖w ω‖ ≤ C)
    (hvar : ∀ᵐ ω ∂μ, (μ[(fun ω => ε ω ^ 2) | F]) ω ≤ σ2) :
    ∀ᵐ ω ∂μ, (μ[(fun ω => (w ω * ε ω) ^ 2) | F]) ω ≤ C ^ 2 * σ2 := by
  have hw2 : ∀ᵐ ω ∂μ, w ω ^ 2 ≤ C ^ 2 := by
    filter_upwards [hC] with ω hω
    exact sq_le_sq.mpr (by simpa only [Real.norm_eq_abs, abs_of_nonneg hC0] using hω)
  have hw2b : ∀ᵐ ω ∂μ, ‖w ω ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [hw2] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (w ω))] using hω
  have hprod : Integrable (fun ω => (w ω * ε ω) ^ 2) μ := by
    simpa only [mul_pow, Pi.pow_apply] using hε2.bdd_mul (hw.pow 2) hw2b
  have hdom : (fun ω => (w ω * ε ω) ^ 2) ≤ᵐ[μ] (fun ω => C ^ 2 * ε ω ^ 2) := by
    filter_upwards [hw2] with ω hω
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hω (sq_nonneg (ε ω))
  have hmono := condExp_mono (m := F) hprod (hε2.const_mul (C ^ 2)) hdom
  have hscale := condExp_smul (μ := μ) (C ^ 2) (fun ω => ε ω ^ 2) F
  filter_upwards [hmono, hscale, hvar] with ω hω1 hω2 hω3
  change (μ[(fun ω => C ^ 2 * ε ω ^ 2) | F]) ω =
    C ^ 2 * (μ[(fun ω => ε ω ^ 2) | F]) ω at hω2
  exact hω1.trans (hω2.le.trans (mul_le_mul_of_nonneg_left hω3 (sq_nonneg C)))

end BFWFluidLimit

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace BFWFluidLimit

/-- The added full-vector conditional independence condition repairs both missing
exploration moments. Integrability follows from the paper's second-moment bound. -/
theorem conditionalIndependence_repairs_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {N : ℕ} (F : MeasurableSpace Ω) (P E : Ω → Fin N → ℝ)
    (hG : F ⊔ MeasurableSpace.comap P inferInstance ≤ mΩ)
    (hind : ∀ φ : (Fin N → ℝ) → ℝ, Measurable φ → Integrable (φ ∘ E) μ →
      μ[φ ∘ E | F ⊔ MeasurableSpace.comap P inferInstance] =ᵐ[μ] μ[φ ∘ E | F])
    (hE : ∀ i, Integrable (fun ω => E ω i) μ)
    (hzero : ∀ i, μ[(fun ω => E ω i) | F] =ᵐ[μ] 0)
    (C : ℝ) (hbound : ∀ᵐ ω ∂μ, ∀ i, ‖P ω i‖ ≤ C) :
    ∀ i, (μ[(fun ω => E ω i) | F ⊔ MeasurableSpace.comap P inferInstance] =ᵐ[μ] 0) ∧
      (μ[(fun ω => P ω i * E ω i) | F] =ᵐ[μ] 0) := by
  intro i
  have hi := NoisePriceConditionallyIndependent.coordinate_exogenous
    (mΩ := mΩ) hind i (hE i) (hzero i)
  refine ⟨hi.2, CurrentPriceExogenous.price_mul_mean_zero (mΩ := mΩ) hG hi i C ?_⟩
  filter_upwards [hbound] with ω hω
  exact hω i

end BFWFluidLimit
open BFWFluidLimit

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {N : ℕ} (F : MeasurableSpace Ω) (P E : Ω → Fin N → ℝ)
    (hG : F ⊔ MeasurableSpace.comap P inferInstance ≤ mΩ)
    (hind : ∀ φ : (Fin N → ℝ) → ℝ, Measurable φ → Integrable (φ ∘ E) μ →
      μ[φ ∘ E | F ⊔ MeasurableSpace.comap P inferInstance] =ᵐ[μ] μ[φ ∘ E | F])
    (hE : ∀ i, Integrable (fun ω => E ω i) μ)
    (hzero : ∀ i, μ[(fun ω => E ω i) | F] =ᵐ[μ] 0)
    (C : ℝ) (hbound : ∀ᵐ ω ∂μ, ∀ i, ‖P ω i‖ ≤ C) :
    ∀ i, (μ[(fun ω => E ω i) | F ⊔ MeasurableSpace.comap P inferInstance] =ᵐ[μ] 0) ∧
      (μ[(fun ω => P ω i * E ω i) | F] =ᵐ[μ] 0) := by
  exact BFWFluidLimit.conditionalIndependence_repairs_moments (mΩ := mΩ) F P E hG hind hE hzero C hbound
