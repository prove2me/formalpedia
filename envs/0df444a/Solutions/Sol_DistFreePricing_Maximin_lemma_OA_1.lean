-- Prove2me | solution 1 for DistFreePricing.Maximin.lemma_OA_1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T16:28:21.42213+00:00
-- url     : https://prove2.me/submissions/5badaea4-749c-4f4f-8a9e-12566db7d914

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

open MeasureTheory
open DistFreePricing.Maximin

namespace Prove2SwarmSubmission

open MeasureTheory

namespace DistFreePricing.Maximin.SA

/-- Strict left tails are contained in the corresponding inclusive tails. -/
theorem strict_tail_le_closed_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → ℝ) (b : ℝ) :
    P.real {ω | X ω < b} ≤ P.real {ω | X ω ≤ b} := by
  change (P {ω | X ω < b}).toReal ≤ (P {ω | X ω ≤ b}).toReal
  apply ENNReal.toReal_mono (measure_ne_top P _)
  exact measure_mono (fun ω (hω : X ω < b) => (le_of_lt hω : X ω ≤ b))

/-- Probability bounds apply to arbitrary events, without a measurability assumption. -/
theorem real_event_le_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Set Ω) : P.real s ≤ 1 := by
  change (P s).toReal ≤ 1
  have hprob : P s ≤ 1 := by
    calc
      P s ≤ P Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top hprob

/-- The permitted zero-threshold case has positive variance and Cantelli bound one. -/
theorem a_form_at_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ σ : ℝ) (hden : 0 < σ ^ 2 + (0 : ℝ) ^ 2) :
    P.real {ω | X ω < μ - 0} ≤ P.real {ω | X ω ≤ μ - 0} ∧
      P.real {ω | X ω ≤ μ - 0} ≤ σ ^ 2 / (σ ^ 2 + (0 : ℝ) ^ 2) := by
  have hσ2 : σ ^ 2 ≠ 0 := ne_of_gt (by simpa using hden)
  refine ⟨strict_tail_le_closed_tail P X (μ - 0), ?_⟩
  simp [hσ2]

/-- It suffices for the Markov core to treat strictly positive deviations.
The zero-deviation case is discharged without using moments or variance identities. -/
theorem a_form_of_positive_core
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ σ : ℝ)
    (hcore : ∀ a : ℝ, 0 < a →
      P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2)) :
    ∀ a : ℝ, 0 ≤ a → 0 < σ ^ 2 + a ^ 2 →
      P.real {ω | X ω < μ - a} ≤ P.real {ω | X ω ≤ μ - a} ∧
        P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2) := by
  intro a ha hden
  by_cases ha0 : a = 0
  · subst a
    exact a_form_at_zero P X μ σ hden
  · exact ⟨strict_tail_le_closed_tail P X (μ - a),
      hcore a (lt_of_le_of_ne ha (Ne.symm ha0))⟩

end DistFreePricing.Maximin.SA

namespace DistFreePricing.Maximin.SA

/-- At the allowed zero threshold, the variance parameter has strictly positive square. -/
theorem threshold_zero_sigma_sq_pos {σ a : ℝ} (ha : a = 0)
    (hden : 0 < σ ^ 2 + a ^ 2) : 0 < σ ^ 2 := by
  simpa [ha] using hden

/-- The denominator condition rules out zero standard deviation at zero threshold. -/
theorem threshold_zero_sigma_ne_zero {σ a : ℝ} (ha : a = 0)
    (hden : 0 < σ ^ 2 + a ^ 2) : σ ≠ 0 := by
  intro hσ
  simp [hσ, ha] at hden

/-- At zero standard deviation, every permitted nonnegative threshold is positive. -/
theorem sigma_zero_threshold_pos {σ a : ℝ} (ha : 0 ≤ a) (hσ : σ = 0)
    (hden : 0 < σ ^ 2 + a ^ 2) : 0 < a := by
  by_contra hnot
  have ha0 : a = 0 := le_antisymm (le_of_not_gt hnot) ha
  simp [hσ, ha0] at hden

/-- The zero-threshold branch has the trivial probability upper bound one. -/
theorem cantelli_ratio_at_zero_threshold {σ a : ℝ} (ha : a = 0)
    (hden : 0 < σ ^ 2 + a ^ 2) : σ ^ 2 / (σ ^ 2 + a ^ 2) = 1 := by
  have hσ2 : σ ^ 2 ≠ 0 := ne_of_gt (threshold_zero_sigma_sq_pos ha hden)
  calc
    σ ^ 2 / (σ ^ 2 + a ^ 2) = σ ^ 2 / σ ^ 2 := by simp [ha]
    _ = 1 := div_self hσ2

/-- This scalar identity does not itself assert that any tail event is null. -/
theorem cantelli_ratio_at_zero_sigma {σ a : ℝ} (hσ : σ = 0) :
    σ ^ 2 / (σ ^ 2 + a ^ 2) = 0 := by
  simp [hσ]

/-- The frozen denominator condition excludes the simultaneous zero case. -/
theorem cantelli_not_both_zero {σ a : ℝ} (hden : 0 < σ ^ 2 + a ^ 2) :
    ¬ (σ = 0 ∧ a = 0) := by
  rintro ⟨hσ, ha⟩
  simp [hσ, ha] at hden

end DistFreePricing.Maximin.SA

namespace DistFreePricing.Maximin.SA

/-- The substitution `a = k * σ` has a positive denominator whenever `σ > 0`.
The scalar fact does not require a sign restriction on `k`. -/
theorem k_scaled_denom_pos {σ : ℝ} (hσ : 0 < σ) (k : ℝ) :
    0 < σ ^ 2 + (k * σ) ^ 2 := by
  positivity

/-- The `a`-form Cantelli ratio at `a = k * σ` is exactly the frozen `k`-form ratio.
Again, only positivity of the standard deviation is needed for this algebra. -/
theorem k_scaled_variance_ratio {σ : ℝ} (hσ : 0 < σ) (k : ℝ) :
    σ ^ 2 / (σ ^ 2 + (k * σ) ^ 2) = 1 / (1 + k ^ 2) := by
  have hden : σ ^ 2 + (k * σ) ^ 2 ≠ 0 :=
    ne_of_gt (k_scaled_denom_pos hσ k)
  have hden' : (1 : ℝ) + k ^ 2 ≠ 0 := ne_of_gt (by positivity)
  apply (div_eq_div_iff hden hden').2
  ring

/-- Pure transfer of the inclusive and strict `a`-form bounds to the exact `k`-form.
No property of the measure or random variable is added: all probability input is in `hA`. -/
theorem k_form_of_a_form
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (μ σ : ℝ)
    (hA : ∀ a : ℝ, 0 ≤ a → 0 < σ ^ 2 + a ^ 2 →
      P.real {ω | X ω < μ - a} ≤ P.real {ω | X ω ≤ μ - a} ∧
        P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2)) :
    0 < σ → ∀ k : ℝ, 0 ≤ k →
      P.real {ω | X ω < μ - k * σ} ≤ P.real {ω | X ω ≤ μ - k * σ} ∧
        P.real {ω | X ω ≤ μ - k * σ} ≤ 1 / (1 + k ^ 2) := by
  intro hσ k hk
  have h := hA (k * σ) (mul_nonneg hk hσ.le) (k_scaled_denom_pos hσ k)
  refine ⟨h.1, ?_⟩
  simpa only [k_scaled_variance_ratio hσ k] using h.2

end DistFreePricing.Maximin.SA

namespace DistFreePricing.Maximin.SA

/-- The two Mathlib-only frozen conclusions, conditional on the owner's positive-deviation core. -/
theorem forms12_of_positive_core
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ σ : ℝ)
    (hcore : ∀ a : ℝ, 0 < a →
      P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2)) :
    (∀ a : ℝ, 0 ≤ a → 0 < σ ^ 2 + a ^ 2 →
      P.real {ω | X ω < μ - a} ≤ P.real {ω | X ω ≤ μ - a} ∧
        P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2)) ∧
    (0 < σ → ∀ k : ℝ, 0 ≤ k →
      P.real {ω | X ω < μ - k * σ} ≤ P.real {ω | X ω ≤ μ - k * σ} ∧
        P.real {ω | X ω ≤ μ - k * σ} ≤ 1 / (1 + k ^ 2)) := by
  have hA := a_form_of_positive_core P X μ σ hcore
  exact ⟨hA, k_form_of_a_form P X μ σ hA⟩

end DistFreePricing.Maximin.SA

namespace DistFreePricing.Maximin.RO

/-- Scalar step of the Markov argument: from `p ≤ q` and `c² q ≤ s c` with `c > 0`, `p ≤ s / c`. -/
theorem div_bound_of_markov {p q c s : ℝ} (hc : 0 < c) (hpq : p ≤ q)
    (hM : c ^ 2 * q ≤ s * c) : p ≤ s / c := by
  rw [le_div_iff₀ hc]
  have h1 : c * (q * c) ≤ c * s := by
    calc c * (q * c) = c ^ 2 * q := by ring
      _ ≤ s * c := hM
      _ = c * s := by ring
  have h2 : q * c ≤ s := by
    exact le_of_mul_le_mul_left h1 hc
  calc p * c ≤ q * c := mul_le_mul_of_nonneg_right hpq hc.le
    _ ≤ s := h2

/-- On the tail `X ≤ μ - a` with `a > 0`, the Markov integrand `(σ² - a (X - μ))²` is at least
`(σ² + a²)²`: with `d = a (μ - a - X) ≥ 0`, the difference of squares is `d (2 (σ² + a²) + d)`. -/
theorem tail_subset_markov_event {Ω : Type*} (X : Ω → ℝ) (μ σ a : ℝ) (ha : 0 < a) :
    {ω | X ω ≤ μ - a} ⊆ {ω | (σ ^ 2 + a ^ 2) ^ 2 ≤ (σ ^ 2 - a * (X ω - μ)) ^ 2} := by
  intro ω hω
  have hx : X ω ≤ μ - a := hω
  have hd : 0 ≤ a * (μ - a - X ω) := mul_nonneg ha.le (sub_nonneg.mpr hx)
  have he : 0 ≤ 2 * (σ ^ 2 + a ^ 2) + a * (μ - a - X ω) := add_nonneg (by positivity) hd
  have key : (σ ^ 2 - a * (X ω - μ)) ^ 2 - (σ ^ 2 + a ^ 2) ^ 2
      = a * (μ - a - X ω) * (2 * (σ ^ 2 + a ^ 2) + a * (μ - a - X ω)) := by ring
  have h3 : 0 ≤ (σ ^ 2 - a * (X ω - μ)) ^ 2 - (σ ^ 2 + a ^ 2) ^ 2 := by
    rw [key]
    exact mul_nonneg hd he
  show (σ ^ 2 + a ^ 2) ^ 2 ≤ (σ ^ 2 - a * (X ω - μ)) ^ 2
  exact sub_nonneg.mp h3

/-- Cantelli's inequality, left tail, for a strictly positive deviation `a` (owner core of
`DistFreePricing.Maximin.lemma_OA_1`). Markov's inequality is applied to `(σ² - a (X - μ))²`,
whose mean is `a² σ² + σ⁴ = σ² (σ² + a²)`. The tail event need not be measurable.
The frozen `0 ≤ σ` is kept in its position for the agreed interface but is not needed, since
only `σ²` occurs; hence `_hσ`. -/
theorem cantelli_core_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (μ σ : ℝ) (hμ : ∫ ω, X ω ∂P = μ) (_hσ : 0 ≤ σ)
    (hvar : ProbabilityTheory.variance X P = σ ^ 2) (a : ℝ) (ha : 0 < a) :
    P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2) := by
  -- Integrability of `X`, `X - μ` and `(X - μ)²`.
  have hXi : Integrable X P := hX.integrable one_le_two
  have hD1 : Integrable (fun ω => X ω - μ) P := hXi.sub (integrable_const μ)
  have hD2 : Integrable (fun ω => (X ω - μ) ^ 2) P := by
    exact (hX.sub (memLp_const μ)).integrable_sq
  -- First and second centred moments.
  have hc1 : ∫ ω, (X ω - μ) ∂P = 0 := by
    rw [integral_sub hXi (integrable_const μ), hμ, integral_const, probReal_univ, one_smul,
          sub_self]
  have hc2 : ∫ ω, (X ω - μ) ^ 2 ∂P = σ ^ 2 := by
    rw [← hvar, ProbabilityTheory.variance_eq_integral hX.aemeasurable, hμ]
  -- The Markov integrand, its integrability and its mean.
  have hpt : ∀ ω, (σ ^ 2 - a * (X ω - μ)) ^ 2
      = a ^ 2 * (X ω - μ) ^ 2 - 2 * a * σ ^ 2 * (X ω - μ) + σ ^ 2 * σ ^ 2 := fun ω => by ring
  have hA : Integrable (fun ω => a ^ 2 * (X ω - μ) ^ 2) P := hD2.const_mul (a ^ 2)
  have hB : Integrable (fun ω => 2 * a * σ ^ 2 * (X ω - μ)) P := hD1.const_mul (2 * a * σ ^ 2)
  have hAB : Integrable (fun ω => a ^ 2 * (X ω - μ) ^ 2 - 2 * a * σ ^ 2 * (X ω - μ)) P :=
    hA.sub hB
  have hABC : Integrable
      (fun ω => a ^ 2 * (X ω - μ) ^ 2 - 2 * a * σ ^ 2 * (X ω - μ) + σ ^ 2 * σ ^ 2) P :=
    hAB.add (integrable_const (σ ^ 2 * σ ^ 2))
  have hYi : Integrable (fun ω => (σ ^ 2 - a * (X ω - μ)) ^ 2) P :=
    hABC.congr (ae_of_all _ (fun ω => (hpt ω).symm))
  have hABCint : ∫ ω, (a ^ 2 * (X ω - μ) ^ 2 - 2 * a * σ ^ 2 * (X ω - μ) + σ ^ 2 * σ ^ 2) ∂P
      = σ ^ 2 * (σ ^ 2 + a ^ 2) := by
    rw [integral_add hAB (integrable_const (σ ^ 2 * σ ^ 2)), integral_sub hA hB,
      integral_const_mul (a ^ 2) (fun ω => (X ω - μ) ^ 2),
      integral_const_mul (2 * a * σ ^ 2) (fun ω => X ω - μ), hc2, hc1]
    (rw [integral_const, probReal_univ, one_smul]; ring)
  have hYint : ∫ ω, (σ ^ 2 - a * (X ω - μ)) ^ 2 ∂P = σ ^ 2 * (σ ^ 2 + a ^ 2) := by
    rw [← hABCint]
    exact integral_congr_ae (ae_of_all _ hpt)
  -- Markov's inequality at level `(σ² + a²)²`.
  have hYnn : 0 ≤ᵐ[P] fun ω => (σ ^ 2 - a * (X ω - μ)) ^ 2 := by
    exact ae_of_all _ (fun ω => sq_nonneg _)
  have hM : (σ ^ 2 + a ^ 2) ^ 2
        * P.real {ω | (σ ^ 2 + a ^ 2) ^ 2 ≤ (σ ^ 2 - a * (X ω - μ)) ^ 2}
      ≤ ∫ ω, (σ ^ 2 - a * (X ω - μ)) ^ 2 ∂P :=
    mul_meas_ge_le_integral_of_nonneg hYnn hYi _
  rw [hYint] at hM
  -- The tail is inside the Markov event.
  have hmono : P.real {ω | X ω ≤ μ - a}
      ≤ P.real {ω | (σ ^ 2 + a ^ 2) ^ 2 ≤ (σ ^ 2 - a * (X ω - μ)) ^ 2} := by
    exact measureReal_mono (tail_subset_markov_event X μ σ a ha)
  have hc : 0 < σ ^ 2 + a ^ 2 := by
    positivity
  exact div_bound_of_markov hc hmono hM

end DistFreePricing.Maximin.RO

namespace DistFreePricing.Maximin.RO

/-- Conjuncts 1 and 2 of `DistFreePricing.Maximin.lemma_OA_1`, verbatim and with the exact frozen
binders: statement-auditor's wrappers applied to the owner's positive-deviation core. -/
theorem lemma_OA_1_forms12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P) (μ σ : ℝ) (hμ : ∫ ω, X ω ∂P = μ)
    (hσ : 0 ≤ σ) (hvar : ProbabilityTheory.variance X P = σ ^ 2) :
    (∀ a : ℝ, 0 ≤ a → 0 < σ ^ 2 + a ^ 2 →
      P.real {ω | X ω < μ - a} ≤ P.real {ω | X ω ≤ μ - a} ∧
        P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2)) ∧
    (0 < σ → ∀ k : ℝ, 0 ≤ k →
      P.real {ω | X ω < μ - k * σ} ≤ P.real {ω | X ω ≤ μ - k * σ} ∧
        P.real {ω | X ω ≤ μ - k * σ} ≤ 1 / (1 + k ^ 2)) :=
  SA.forms12_of_positive_core P X μ σ
    (fun a ha => cantelli_core_pos P X hX μ σ hμ hσ hvar a ha)

/-- The k-form on `(ℝ, P)`, stated with exactly the premise type of source-scout's
`SS.conj3_of_kform`, so that conjunct 3 needs no lambda over an instance binder. -/
theorem kform_real (μ σ : ℝ) :
    ∀ (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℝ → ℝ), MemLp X 2 P →
      ∫ ω, X ω ∂P = μ → 0 ≤ σ → ProbabilityTheory.variance X P = σ ^ 2 → 0 < σ →
        ∀ k : ℝ, 0 ≤ k →
          P.real {ω | X ω < μ - k * σ} ≤ P.real {ω | X ω ≤ μ - k * σ} ∧
            P.real {ω | X ω ≤ μ - k * σ} ≤ 1 / (1 + k ^ 2) := by
  intro P _ X hX hμ hσ hvar
  exact (lemma_OA_1_forms12 P X hX μ σ hμ hσ hvar).2

end DistFreePricing.Maximin.RO

/-! ## source-scout piece SS: conjunct 3 bridge for `lemma_OA_1`

This is the final-packet variant: it imports the public module
`Definitions.Def_DistFreePricing_Maximin_Setting` (code sha256 950646ac…) and contains no inline copy. It takes no extra hypotheses: from `F ∈ valClass μ σ` alone it derives the
probability-measure instance, `MemLp id 2 F`, the mean `μ` and the variance `σ ^ 2`, and then
transfers any k-form Cantelli bound for `fun v => v` on `(ℝ, F)` to the `Iio`/`Iic` masses. -/

namespace DistFreePricing.Maximin.SS

open MeasureTheory ProbabilityTheory

theorem isProbabilityMeasure_of_mem {μ σ : ℝ} {F : Measure ℝ} (hF : F ∈ valClass μ σ) :
    IsProbabilityMeasure F := by
  obtain ⟨h1, -, -, -, -, -⟩ := hF
  exact h1

theorem memLp_id_of_mem {μ σ : ℝ} {F : Measure ℝ} (hF : F ∈ valClass μ σ) :
    MemLp (fun v : ℝ => v) 2 F := by
  obtain ⟨-, -, -, h4, -, -⟩ := hF
  exact (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2 h4

theorem integral_id_of_mem {μ σ : ℝ} {F : Measure ℝ} (hF : F ∈ valClass μ σ) :
    ∫ v, v ∂F = μ := by
  obtain ⟨-, -, -, -, h5, -⟩ := hF
  exact h5

theorem variance_id_of_mem {μ σ : ℝ} {F : Measure ℝ} (hF : F ∈ valClass μ σ) :
    variance (fun v : ℝ => v) F = σ ^ 2 := by
  have hP : IsProbabilityMeasure F := isProbabilityMeasure_of_mem hF
  have hm : MemLp (fun v : ℝ => v) 2 F := memLp_id_of_mem hF
  obtain ⟨-, -, -, -, h5, h6⟩ := hF
  rw [variance_eq_sub hm]
  show (∫ v, v ^ 2 ∂F) - (∫ v, v ∂F) ^ 2 = σ ^ 2
  rw [h6, h5]
  ring

/-- Conjunct 3 of `lemma_OA_1`, assuming the k-form (conjunct 2) for an arbitrary probability measure
and real random variable. The owner instantiates `hkform` with its proved Cantelli k-form. -/
theorem conj3_of_kform (μ σ : ℝ)
    (hkform : ∀ (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℝ → ℝ), MemLp X 2 P →
      ∫ ω, X ω ∂P = μ → 0 ≤ σ → variance X P = σ ^ 2 → 0 < σ → ∀ k : ℝ, 0 ≤ k →
        P.real {ω | X ω < μ - k * σ} ≤ P.real {ω | X ω ≤ μ - k * σ} ∧
          P.real {ω | X ω ≤ μ - k * σ} ≤ 1 / (1 + k ^ 2)) :
    0 < σ → ∀ F ∈ valClass μ σ, ∀ k : ℝ, 0 ≤ k →
      F.real (Set.Iio (μ - k * σ)) ≤ F.real (Set.Iic (μ - k * σ)) ∧
        F.real (Set.Iic (μ - k * σ)) ≤ 1 / (1 + k ^ 2) := by
  intro hσ F hF k hk
  have hP : IsProbabilityMeasure F := isProbabilityMeasure_of_mem hF
  exact hkform F (fun v => v) (memLp_id_of_mem hF) (integral_id_of_mem hF) hσ.le
    (variance_id_of_mem hF) hσ k hk

end DistFreePricing.Maximin.SS

namespace DistFreePricing.Maximin

open MeasureTheory

/-- Lemma OA.1 (Cantelli's inequality, OA p. 9), for a square-integrable random variable with
mean `μ` and standard deviation `σ ≥ 0`: the `a`-form for every `a ≥ 0` at which the bound
`σ²/(σ² + a²)` is defined, and, under the paper's standing `σ > 0`, the equivalent `k`-form, also
for a valuation law `F ∈ 𝓕`. -/
theorem lemma_OA_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (μ σ : ℝ) (hμ : ∫ ω, X ω ∂P = μ) (hσ : 0 ≤ σ)
    (hvar : ProbabilityTheory.variance X P = σ ^ 2) :
    (∀ a : ℝ, 0 ≤ a → 0 < σ ^ 2 + a ^ 2 →
      P.real {ω | X ω < μ - a} ≤ P.real {ω | X ω ≤ μ - a} ∧
        P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2)) ∧
    (0 < σ → ∀ k : ℝ, 0 ≤ k →
      P.real {ω | X ω < μ - k * σ} ≤ P.real {ω | X ω ≤ μ - k * σ} ∧
        P.real {ω | X ω ≤ μ - k * σ} ≤ 1 / (1 + k ^ 2)) ∧
    (0 < σ → ∀ F ∈ valClass μ σ, ∀ k : ℝ, 0 ≤ k →
      F.real (Set.Iio (μ - k * σ)) ≤ F.real (Set.Iic (μ - k * σ)) ∧
        F.real (Set.Iic (μ - k * σ)) ≤ 1 / (1 + k ^ 2)) := by
  have h12 := RO.lemma_OA_1_forms12 P X hX μ σ hμ hσ hvar
  exact ⟨h12.1, h12.2, SS.conj3_of_kform μ σ (RO.kform_real μ σ)⟩

end DistFreePricing.Maximin

end Prove2SwarmSubmission

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (μ σ : ℝ) (hμ : ∫ ω, X ω ∂P = μ) (hσ : 0 ≤ σ)
    (hvar : ProbabilityTheory.variance X P = σ ^ 2) :
    (∀ a : ℝ, 0 ≤ a → 0 < σ ^ 2 + a ^ 2 →
      P.real {ω | X ω < μ - a} ≤ P.real {ω | X ω ≤ μ - a} ∧
        P.real {ω | X ω ≤ μ - a} ≤ σ ^ 2 / (σ ^ 2 + a ^ 2)) ∧
    (0 < σ → ∀ k : ℝ, 0 ≤ k →
      P.real {ω | X ω < μ - k * σ} ≤ P.real {ω | X ω ≤ μ - k * σ} ∧
        P.real {ω | X ω ≤ μ - k * σ} ≤ 1 / (1 + k ^ 2)) ∧
    (0 < σ → ∀ F ∈ valClass μ σ, ∀ k : ℝ, 0 ≤ k →
      F.real (Set.Iio (μ - k * σ)) ≤ F.real (Set.Iic (μ - k * σ)) ∧
        F.real (Set.Iic (μ - k * σ)) ≤ 1 / (1 + k ^ 2)) := by
  exact _root_.Prove2SwarmSubmission.DistFreePricing.Maximin.lemma_OA_1 P X hX μ σ hμ hσ hvar
