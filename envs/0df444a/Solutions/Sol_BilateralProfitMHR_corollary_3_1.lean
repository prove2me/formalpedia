-- Prove2me | solution 1 for BilateralProfitMHR.corollary_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T17:15:31.381733+00:00
-- url     : https://prove2.me/submissions/63088e71-0f86-4f6a-8e59-f974a2d85844

import Mathlib
import Definitions.Def_LG2021_CanonicalBandit
import Theorems.Thm_LG2021_john_normalized_bandit

set_option autoImplicit false

section

namespace BilateralProfitMHR.CorollaryTransport

open MeasureTheory
open scoped ENNReal

private theorem exists_admissible_scale_lt {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) {γ r : ℝ}
    (hr : 0 < r) (hγr : γ < r)
    (hX : HighDimProb.Concentration.subgaussianNorm P X ≤ ENNReal.ofReal γ) :
    ∃ t : ℝ, 0 < t ∧ t < r ∧
      Integrable (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) P ∧
      (∫ ω, Real.exp ((X ω) ^ 2 / t ^ 2) ∂P) ≤ 2 := by
  have hlt : HighDimProb.Concentration.subgaussianNorm P X < ENNReal.ofReal r :=
    lt_of_le_of_lt hX ((ENNReal.ofReal_lt_ofReal_iff hr).2 hγr)
  simp only [HighDimProb.Concentration.subgaussianNorm, iInf_lt_iff] at hlt
  obtain ⟨t, ht, hint, hmoment, htr⟩ := hlt
  exact ⟨t, ht, (ENNReal.ofReal_lt_ofReal_iff hr).1 htr, hint, hmoment⟩

private theorem exp_square_moment_of_norm_lt {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hXm : Measurable X) {γ r : ℝ}
    (hr : 0 < r) (hγr : γ < r)
    (hX : HighDimProb.Concentration.subgaussianNorm P X ≤ ENNReal.ofReal γ) :
    Integrable (fun ω => Real.exp ((X ω) ^ 2 / r ^ 2)) P ∧
      (∫ ω, Real.exp ((X ω) ^ 2 / r ^ 2) ∂P) ≤ 2 := by
  obtain ⟨t, ht, htr, hint, hmoment⟩ := exists_admissible_scale_lt P X hr hγr hX
  have hdom : ∀ ω, Real.exp ((X ω) ^ 2 / r ^ 2) ≤
      Real.exp ((X ω) ^ 2 / t ^ 2) := by
    intro ω
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos ht)
      (sq_le_sq₀ ht.le hr.le |>.2 htr.le)
  have hint' : Integrable (fun ω => Real.exp ((X ω) ^ 2 / r ^ 2)) P :=
    hint.mono' (by fun_prop) (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hdom ω)
  exact ⟨hint', (integral_mono hint' hint hdom).trans hmoment⟩

private noncomputable def normalizationScale (ℓ γ : ℝ) : ℝ :=
  2 * max 1 (max ℓ γ)

private theorem normalizationScale_pos (ℓ γ : ℝ) : 0 < normalizationScale ℓ γ := by
  unfold normalizationScale
  have : (1 : ℝ) ≤ max 1 (max ℓ γ) := le_max_left _ _
  linarith

private theorem lt_normalizationScale (ℓ γ : ℝ) : γ < normalizationScale ℓ γ := by
  unfold normalizationScale
  have h1 : (1 : ℝ) ≤ max 1 (max ℓ γ) := le_max_left _ _
  have hγ : γ ≤ max 1 (max ℓ γ) := (le_max_right ℓ γ).trans (le_max_right _ _)
  linarith

private theorem normalizationScale_le (ℓ γ : ℝ) (hγ : 0 ≤ γ) :
    normalizationScale ℓ γ ≤ 2 * max 1 ℓ * (1 + γ) := by
  have hm : (1 : ℝ) ≤ max 1 ℓ := le_max_left _ _
  have hℓ : ℓ ≤ max 1 ℓ := le_max_right _ _
  have hprod : 0 ≤ max 1 ℓ * γ := mul_nonneg (by linarith) hγ
  have hγprod : γ ≤ max 1 ℓ * γ := by nlinarith
  unfold normalizationScale
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply max_le
  · nlinarith
  · apply max_le <;> nlinarith

private theorem cumLoss_mul (X Ω : Type) [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss A ν (fun x => c * g x) ω m τ y = c * cumLoss A ν g ω m τ y := by
  induction m generalizing τ with
  | zero => simp [cumLoss]
  | succ m ih =>
      simp only [cumLoss, ih, lintegral_const_mul' c _ hc, mul_add]

private theorem expectedCumLoss_mul (X Ω : Type) [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (n : ℕ) :
    expectedCumLoss A P ν (fun x => c * g x) n = c * expectedCumLoss A P ν g n := by
  simp only [expectedCumLoss, cumLoss_mul X Ω A ν g c hc,
    lintegral_const_mul' c _ hc]

private noncomputable def observationEquiv (b S : ℝ) (hS : S ≠ 0) : ℝ ≃ᵐ ℝ where
  toFun z := (z - b) / S
  invFun z := S * z + b
  left_inv z := by field_simp; ring
  right_inv z := by field_simp; ring
  measurable_toFun := by change Measurable (fun z : ℝ => (z - b) / S); fun_prop
  measurable_invFun := by change Measurable (fun z : ℝ => S * z + b); fun_prop

section Observations

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]

private noncomputable def rescaleQuery (A : QueryAlg X Ω) (b S : ℝ) : QueryAlg X Ω where
  query τ ω y := A.query τ ω (fun i => (y i - b) / S)
  query_measurable τ := (A.query_measurable τ).comp
    (show Measurable (fun z : Ω × (Fin τ → ℝ) => (z.1, fun i => (z.2 i - b) / S)) from by
      fun_prop)

private noncomputable def normalizeKernel (ν : ObsKernel X) (b S : ℝ) : ObsKernel X :=
  fun τ xs ys x => (ν τ xs (fun i => S * ys i + b) x).map (fun z => (z - b) / S)

private theorem rescaleQuery_isOn (A : QueryAlg X Ω) (b S : ℝ) {K : Set X}
    (hA : A.IsOn K) : (rescaleQuery A b S).IsOn K := by
  intro τ ω y
  exact hA τ ω (fun i => (y i - b) / S)

private theorem cumLoss_rescaleQuery (A : QueryAlg X Ω) (ν : ObsKernel X)
    (b S : ℝ) (hS : S ≠ 0) (g : X → ℝ≥0∞)
    (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss (rescaleQuery A b S) ν g ω m τ y =
      cumLoss A (normalizeKernel ν b S) g ω m τ (fun i => (y i - b) / S) := by
  induction m generalizing τ with
  | zero => rfl
  | succ m ih =>
      simp only [cumLoss, rescaleQuery]
      congr 1
      let e := observationEquiv b S hS
      have hhist : (fun i : Fin τ => S * ((y i - b) / S) + b) = y := by
        funext i
        field_simp
        ring
      have hpast : (rescaleQuery A b S).pastQueries ω y =
          A.pastQueries ω (fun i => (y i - b) / S) := by
        funext i
        rfl
      rw [show normalizeKernel ν b S τ (A.pastQueries ω (fun i => (y i - b) / S))
          (fun i => (y i - b) / S) (A.query τ ω (fun i => (y i - b) / S)) =
          (ν τ ((rescaleQuery A b S).pastQueries ω y) y
            (A.query τ ω (fun i => (y i - b) / S))).map e by
        simp only [normalizeKernel, hhist, hpast]
        rfl]
      rw [lintegral_map_equiv]
      apply lintegral_congr
      intro z
      change cumLoss (rescaleQuery A b S) ν g ω m (τ + 1) (Fin.snoc y z) = _
      rw [ih]
      congr 1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [e, observationEquiv]

private theorem expectedCumLoss_rescaleQuery (A : QueryAlg X Ω) (P : Measure Ω)
    (ν : ObsKernel X) (b S : ℝ) (hS : S ≠ 0) (g : X → ℝ≥0∞) (n : ℕ) :
    expectedCumLoss (rescaleQuery A b S) P ν g n =
      expectedCumLoss A P (normalizeKernel ν b S) g n := by
  apply lintegral_congr
  intro ω
  convert cumLoss_rescaleQuery A ν b S hS g ω n 0 Fin.elim0 using 1
  congr 1
  funext i
  exact Fin.elim0 i

end Observations

end BilateralProfitMHR.CorollaryTransport

end

section

namespace BilateralProfitMHR.CorollaryTransport

open MeasureTheory
open scoped ENNReal

/-- The normalized observation condition used by the stochastic convex-bandit argument:
centered observations have exponential square moment at most two. -/
private theorem normalizeKernel_measurable {X : Type} [MeasurableSpace X]
    (ν : ObsKernel X) (hν : ν.IsMeasurable) (b S : ℝ) :
    (normalizeKernel ν b S).IsMeasurable := by
  intro τ
  change Measurable (fun w : (Fin τ → X) × (Fin τ → ℝ) × X =>
    (ν τ w.1 (fun i => S * w.2.1 i + b) w.2.2).map (fun z => (z - b) / S))
  apply (Measure.measurable_map (fun z : ℝ => (z - b) / S) (by fun_prop)).comp
  exact (hν τ).comp (show Measurable (fun w : (Fin τ → X) × (Fin τ → ℝ) × X =>
    (w.1, (fun i => S * w.2.1 i + b), w.2.2)) from by fun_prop)

private theorem normalize_observation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (b m γ S : ℝ) (hS : 0 < S) (hγS : γ < S)
    (hi : Integrable (fun z : ℝ => z) μ) (hm : (∫ z, z ∂μ) = m)
    (hn : HighDimProb.Concentration.subgaussianNorm μ (fun z => z - m) ≤
      ENNReal.ofReal γ) :
    let μ' := μ.map (fun z => (z - b) / S)
    IsProbabilityMeasure μ' ∧ Integrable (fun z : ℝ => z) μ' ∧
      (∫ z, z ∂μ') = (m - b) / S ∧
      Integrable (fun z : ℝ => Real.exp ((z - (m - b) / S) ^ 2)) μ' ∧
      (∫ z, Real.exp ((z - (m - b) / S) ^ 2) ∂μ') ≤ 2 := by
  let e := observationEquiv b S (ne_of_gt hS)
  change IsProbabilityMeasure (μ.map e) ∧ Integrable (fun z : ℝ => z) (μ.map e) ∧
    (∫ z, z ∂(μ.map e)) = (m - b) / S ∧
    Integrable (fun z : ℝ => Real.exp ((z - (m - b) / S) ^ 2)) (μ.map e) ∧
    (∫ z, Real.exp ((z - (m - b) / S) ^ 2) ∂(μ.map e)) ≤ 2
  refine ⟨Measure.isProbabilityMeasure_map e.measurable.aemeasurable, ?_, ?_, ?_⟩
  · rw [integrable_map_equiv]
    exact (hi.sub (integrable_const b)).div_const S
  · rw [integral_map_equiv]
    change (∫ z, (z - b) / S ∂μ) = _
    rw [integral_div, integral_sub hi (integrable_const b), hm]
    simp
  · obtain ⟨hei, hem⟩ := exp_square_moment_of_norm_lt μ (fun z => z - m)
      (by fun_prop) hS hγS hn
    have heq : (fun z : ℝ => Real.exp ((e z - (m - b) / S) ^ 2)) =
        (fun z => Real.exp ((z - m) ^ 2 / S ^ 2)) := by
      funext z
      congr 1
      dsimp [e, observationEquiv]
      field_simp
      <;> ring
    constructor
    · rw [integrable_map_equiv]
      change Integrable (fun z : ℝ => Real.exp ((e z - (m - b) / S) ^ 2)) μ
      rw [heq]
      exact hei
    · rw [integral_map_equiv, heq]
      exact hem

private theorem normalizeKernel_unitNoiseCond {X : Type} [MeasurableSpace X]
    (ν : ObsKernel X) {K : Set X} (L : X → ℝ) (b γ S : ℝ)
    (hS : 0 < S) (hγS : γ < S) (hν : NoiseCond K L γ ν) :
    UnitNoiseCond K (fun x => (L x - b) / S) (normalizeKernel ν b S) := by
  intro τ xs ys x hxs hx
  obtain ⟨hp, hi, hm, hn⟩ := hν τ xs (fun i => S * ys i + b) x hxs hx
  letI := hp
  exact normalize_observation (ν τ xs (fun i => S * ys i + b) x)
    b (L x) γ S hS hγS hi hm hn

private theorem unitNoiseCond_noiseCond {X : Type} (K : Set X) (L : X → ℝ)
    (ν : ObsKernel X) (hν : UnitNoiseCond K L ν) : NoiseCond K L 1 ν := by
  intro τ xs ys x hxs hx
  obtain ⟨hp, hi, hm, hei, hem⟩ := hν τ xs ys x hxs hx
  refine ⟨hp, hi, hm, ?_⟩
  unfold HighDimProb.Concentration.subgaussianNorm
  refine iInf_le_of_le 1 (iInf_le_of_le (by norm_num) ?_)
  refine iInf_le_of_le (by simpa using hei) (iInf_le_of_le (by simpa using hem) ?_)
  rfl


private theorem le_normalizationScale (ℓ γ : ℝ) : ℓ ≤ normalizationScale ℓ γ := by
  unfold normalizationScale
  have h1 : (1 : ℝ) ≤ max 1 (max ℓ γ) := le_max_left _ _
  have hℓ : ℓ ≤ max 1 (max ℓ γ) := (le_max_left ℓ γ).trans (le_max_right _ _)
  linarith

private theorem normalizedLoss_range {X : Type} {K : Set X} {L : X → ℝ}
    {b ℓ S : ℝ} (hS : 0 < S) (hℓS : ℓ ≤ S)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc b (b + ℓ)) :
    ∀ x ∈ K, (L x - b) / S ∈ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hL x hx
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hS.le
  · apply (div_le_one hS).2
    linarith

private theorem normalizedLoss_convex {E : Type} [AddCommGroup E] [Module ℝ E]
    {K : Set E} {L : E → ℝ} (hL : ConvexOn ℝ K L) (b S : ℝ) (hS : 0 < S) :
    ConvexOn ℝ K (fun x => (L x - b) / S) := by
  simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, sub_eq_add_neg, div_eq_mul_inv, mul_comm] using
    ConvexOn.smul (inv_nonneg.mpr hS.le) (hL.add_const (-b))

private theorem sInf_normalizedLoss {X : Type} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (L : X → ℝ) (hL : ContinuousOn L K)
    (b S : ℝ) (hS : 0 < S) :
    sInf ((fun x => (L x - b) / S) '' K) = (sInf (L '' K) - b) / S := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hL
  have hleast : IsLeast (L '' K) (L x) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hmin hz
  have hleast' : IsLeast ((fun x => (L x - b) / S) '' K) ((L x - b) / S) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hmin hz) b) hS.le
  rw [hleast.csInf_eq, hleast'.csInf_eq]

private theorem normalized_regret_identity {X : Type} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (L : X → ℝ) (hL : ContinuousOn L K)
    (b S : ℝ) (hS : 0 < S) (x : X) :
    ENNReal.ofReal (L x - sInf (L '' K)) = ENNReal.ofReal S *
      ENNReal.ofReal ((L x - b) / S - sInf ((fun x => (L x - b) / S) '' K)) := by
  rw [sInf_normalizedLoss hK hne L hL b S hS, ← ENNReal.ofReal_mul hS.le]
  congr 1
  field_simp
  <;> ring

private theorem expectedRegret_rescaleQuery {X Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Ω] [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (L : X → ℝ) (hL : ContinuousOn L K)
    (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X)
    (b S : ℝ) (hS : 0 < S) (n : ℕ) :
    expectedCumLoss (rescaleQuery A b S) P ν
      (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n =
    ENNReal.ofReal S * expectedCumLoss A P (normalizeKernel ν b S)
      (fun x => ENNReal.ofReal ((L x - b) / S -
        sInf ((fun x => (L x - b) / S) '' K))) n := by
  rw [expectedCumLoss_rescaleQuery A P ν b S (ne_of_gt hS)]
  have hcost : (fun x => ENNReal.ofReal (L x - sInf (L '' K))) =
      (fun x => ENNReal.ofReal S * ENNReal.ofReal ((L x - b) / S -
        sInf ((fun x => (L x - b) / S) '' K))) := by
    funext x
    exact normalized_regret_identity hK hne L hL b S hS x
  rw [hcost, expectedCumLoss_mul X Ω A P (normalizeKernel ν b S)
    _ (ENNReal.ofReal S) ENNReal.ofReal_ne_top]


end BilateralProfitMHR.CorollaryTransport

end

section
namespace LG2021
open BilateralProfitMHR.CorollaryTransport
private theorem normalization_rate_bound (ℓ γ D : ℝ) (n : ℕ) (hγ : 0 ≤ γ) (hD : 0 ≤ D) :
    normalizationScale ℓ γ * (D * Real.sqrt n * Real.log n ^ 2) ≤
      (2 * max 1 ℓ * D) * (1 + γ) * Real.sqrt n * Real.log n ^ 2 := by
  have hnonneg : 0 ≤ D * Real.sqrt n * Real.log n ^ 2 := by positivity
  calc
    _ ≤ (2 * max 1 ℓ * (1 + γ)) * (D * Real.sqrt n * Real.log n ^ 2) :=
      mul_le_mul_of_nonneg_right (normalizationScale_le ℓ γ hγ) hnonneg
    _ = _ := by ring


end LG2021

end

section

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set

/-- Loss and observation normalization from the unit-range fixed-dimensional
theorem to the exact convex-bandit corollary. The normalization scale is known
before the unknown loss and the adaptive observation law are supplied. -/
private theorem corollary_3_1_of_normalized_bandit
    (hsource : ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ K : Set (EuclideanSpace ℝ (Fin d)), K.Nonempty → IsCompact K → Convex ℝ K →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
            ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
              ContinuousOn L K → ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
              ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable → UnitNoiseCond K L ν →
                expectedCumLoss A P ν (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal (C * Real.sqrt n * Real.log n ^ 2)) :
    ∀ (d : ℕ) (ℓ : ℝ), 0 < ℓ → ∃ C : ℝ, ∀ K : Set (EuclideanSpace ℝ (Fin d)),
      K.Nonempty → IsCompact K → Convex ℝ K → ∀ (b γ : ℝ), 0 ≤ γ → ∀ n : ℕ, 2 ≤ n →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
            ∀ L : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn L K → ConvexOn ℝ K L →
              (∀ x ∈ K, L x ∈ Icc b (b + ℓ)) →
              ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable → NoiseCond K L γ ν →
                expectedCumLoss A P ν (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal (C * (1 + γ) * Real.sqrt n * Real.log n ^ 2) := by
  intro d ℓ hℓ
  obtain ⟨C, hC, hsource⟩ := hsource d
  refine ⟨2 * max 1 ℓ * C, ?_⟩
  intro K hne hK hcv b γ hγ n hn
  obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ := hsource n hn K hne hK hcv
  letI := mΩ
  let S := normalizationScale ℓ γ
  have hS : 0 < S := normalizationScale_pos ℓ γ
  refine ⟨Ω, mΩ, P, hP, rescaleQuery A b S, rescaleQuery_isOn A b S hA, ?_⟩
  intro L hLc hLv hLr ν hνm hν
  have hnormc : ContinuousOn (fun x => (L x - b) / S) K :=
    (hLc.sub continuousOn_const).div_const S
  have hnormv := normalizedLoss_convex hLv b S hS
  have hnormr := normalizedLoss_range hS (le_normalizationScale ℓ γ) hLr
  have hnoise := normalizeKernel_unitNoiseCond ν L b γ S hS (lt_normalizationScale ℓ γ) hν
  have hmeas := normalizeKernel_measurable ν hνm b S
  have hb := hregret _ hnormc hnormv hnormr _ hmeas hnoise
  rw [expectedRegret_rescaleQuery hK hne L hLc A P ν b S hS]
  calc
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal (C * Real.sqrt n * Real.log n ^ 2) := by gcongr
    _ = ENNReal.ofReal (S * (C * Real.sqrt n * Real.log n ^ 2)) :=
      (ENNReal.ofReal_mul hS.le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (normalization_rate_bound ℓ γ C n hγ hC)

end LG2021

end

open MeasureTheory BilateralProfitMHR

/-- Corollary 3.1 with its exact original quantifiers. The proof imports the
formalized fixed-dimensional Lattimore--Gyorgy theorem. It uses the known scale
`2 * max 1 (max ℓ γ)` to normalize loss and observations, proving the exact
adaptive-kernel and expected-regret identities. In particular, the algorithm
is selected before the unknown loss and noise law. The Gaussian separation
argument and measurable policy construction are adapted for formalization in
the imported theorem; this conclusion retains the requested regret rate. -/
theorem solution :
    ∀ (d : ℕ) (ℓ : ℝ), 0 < ℓ → ∃ C : ℝ, ∀ (K : Set (EuclideanSpace ℝ (Fin d))),
      K.Nonempty → IsCompact K → Convex ℝ K → ∀ (b γ : ℝ), 0 ≤ γ → ∀ n : ℕ, 2 ≤ n →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
            ∀ L : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn L K → ConvexOn ℝ K L →
              (∀ x ∈ K, L x ∈ Set.Icc b (b + ℓ)) →
              ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable → NoiseCond K L γ ν →
                expectedCumLoss A P ν (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal (C * (1 + γ) * Real.sqrt n * Real.log n ^ 2) := by
  exact LG2021.corollary_3_1_of_normalized_bandit LG2021.john_normalized_bandit
