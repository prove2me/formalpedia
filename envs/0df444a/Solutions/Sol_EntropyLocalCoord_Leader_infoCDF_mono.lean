-- Prove2me | solution 1 for EntropyLocalCoord.Leader.infoCDF_mono
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:34.302369+00:00
-- url     : https://prove2.me/submissions/a0fef065-9e7d-43af-a974-68b469f1f48d

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model
import Definitions.Def_EntropyLocalCoord_Leader_Information

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace EntropyLocalCoord.Dev.CDF

open EntropyLocalCoord.Leader

section General

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSingletonClass β]
  (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → β)

lemma condProb_nonneg_le {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hX : Measurable[mΩ] X) (b : β) :
    ∀ᵐ ω ∂P, 0 ≤ condProb m P X b ω ∧ condProb m P X b ω ≤ 1 := by
  have hint : Integrable ((X ⁻¹' {b}).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton b))
  have h0 : 0 ≤ᵐ[P] P[(X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) | m] :=
    condExp_nonneg (Filter.Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω))
  have h1 : P[(X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[P] P[(fun _ => (1 : ℝ)) | m] :=
    condExp_mono hint (integrable_const _)
      (Filter.Eventually.of_forall (fun ω => Set.indicator_le_self' (fun _ _ => zero_le_one) ω))
  rw [condExp_const hm] at h1
  filter_upwards [h0, h1] with ω a b
  exact ⟨a, b⟩

lemma condProb_of_not_mem_range (m : MeasurableSpace Ω) (b : β) (hb : b ∉ Set.range X) :
    condProb m P X b = 0 := by
  have : X ⁻¹' {b} = ∅ := by
    ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h => hb ⟨ω, h⟩
  unfold condProb
  rw [this, Set.indicator_empty]
  exact condExp_zero

lemma integrable_negMulLog_condProb {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hX : Measurable[mΩ] X)
    (b : β) : Integrable (fun ω => Real.negMulLog (condProb m P X b ω)) P := by
  have hsm : AEStronglyMeasurable[mΩ] (condProb m P X b) P :=
    (stronglyMeasurable_condExp (m := m) (f := (X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)))
      (μ := P)).mono hm |>.aestronglyMeasurable
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (Real.continuous_negMulLog.comp_aestronglyMeasurable hsm) ?_
  filter_upwards [condProb_nonneg_le P X hm hX b] with ω ⟨h0, h1⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg h0 h1)]
  have := Real.negMulLog_le_one_sub_self h0
  linarith

/-- `H(X | m) · log 2` as a finite sum of integrals (for finite-valued measurable `X`). -/
lemma condEntropy_mul_log (hfin : (Set.range X).Finite) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hX : Measurable[mΩ] X) :
    condEntropy m P X * Real.log 2 =
      ∑ b ∈ hfin.toFinset, ∫ ω, Real.negMulLog (condProb m P X b ω) ∂P := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold condEntropy
  rw [div_mul_cancel₀ _ hlog, ← integral_finsetSum]
  · congr 1
    ext ω
    apply finsum_eq_sum_of_support_subset
    intro b hb
    simp only [Function.mem_support] at hb
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra h
    apply hb
    simp [condProb_of_not_mem_range P X m b h]
  · intro b _
    exact integrable_negMulLog_condProb P X hm hX b

/-- Conditioning reduces entropy: `H(X | m₂) ≤ H(X | m₁)` for `m₁ ≤ m₂`. -/
theorem condEntropy_anti (hfin : (Set.range X).Finite) (hX : Measurable[mΩ] X)
    {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ mΩ) :
    condEntropy m₂ P X ≤ condEntropy m₁ P X := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : m₁ ≤ mΩ := h12.trans h2
  refine le_of_mul_le_mul_right ?_ hlog
  rw [condEntropy_mul_log P X hfin h2 hX, condEntropy_mul_log P X hfin h1 hX]
  refine Finset.sum_le_sum (fun b _ => ?_)
  have hint : Integrable ((X ⁻¹' {b}).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton b))
  set p2 := condProb m₂ P X b with hp2
  have hp2int : Integrable p2 P := integrable_condExp
  have hu : UpperSemicontinuousOn Real.negMulLog (Set.Ici 0) :=
    Real.continuous_negMulLog.continuousOn.upperSemicontinuousOn
  have hjen : P[(Real.negMulLog ∘ p2) | m₁] ≤ᵐ[P] Real.negMulLog ∘ P[p2 | m₁] := by
    refine Real.concaveOn_negMulLog.condExp_map_le h1 hu
      ?_ isClosed_Ici hp2int (integrable_negMulLog_condProb P X h2 hX b)
    filter_upwards [condProb_nonneg_le P X h2 hX b] with ω h
    exact h.1
  have hcc : P[p2 | m₁] =ᵐ[P] condProb m₁ P X b := condExp_condExp_of_le h12 h2
  calc ∫ ω, Real.negMulLog (p2 ω) ∂P = ∫ ω, (P[(Real.negMulLog ∘ p2) | m₁]) ω ∂P :=
        (integral_condExp h1).symm
    _ ≤ ∫ ω, (Real.negMulLog ∘ P[p2 | m₁]) ω ∂P := by
        refine integral_mono_ae integrable_condExp ?_ hjen
        have : Integrable (Real.negMulLog ∘ condProb m₁ P X b) P :=
          integrable_negMulLog_condProb P X h1 hX b
        refine this.congr ?_
        filter_upwards [hcc] with ω h
        simp [h]
    _ = ∫ ω, Real.negMulLog (condProb m₁ P X b ω) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hcc] with ω h
        simp [h]

/-- Trivial σ-algebra: conditional entropy is the entropy. -/
theorem condEntropy_bot (hX : Measurable[mΩ] X) :
    condEntropy ⊥ P X = entropy P X := by
  unfold condEntropy entropy
  congr 1
  have h : ∀ b, condProb ⊥ P X b = fun _ => P.real (X ⁻¹' {b}) := by
    intro b
    unfold condProb
    rw [condExp_bot]
    funext ω
    rw [integral_indicator_const _ (hX (measurableSet_singleton b))]
    simp
  simp_rw [h]
  simp

/-- If `X` is `m`-measurable then `H(X | m) = 0`. -/
theorem condEntropy_of_measurable (hfin : (Set.range X).Finite) {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (hXm : Measurable[m] X) : condEntropy m P X = 0 := by
  have hX : Measurable[mΩ] X := hXm.mono hm le_rfl
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have := condEntropy_mul_log P X hfin hm hX
  have h0 : ∀ b ∈ hfin.toFinset, ∫ ω, Real.negMulLog (condProb m P X b ω) ∂P = 0 := by
    intro b _
    have hind : condProb m P X b = (X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) := by
      unfold condProb
      refine condExp_of_stronglyMeasurable hm ?_ ?_
      · exact (measurable_const.indicator (hXm (measurableSet_singleton b))).stronglyMeasurable
      · exact (integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton b))
    rw [hind]
    have : ∀ ω, Real.negMulLog ((X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) ω) = 0 := by
      intro ω
      by_cases h : ω ∈ X ⁻¹' {b} <;> simp [h]
    simp [this]
  rw [Finset.sum_eq_zero h0] at this
  exact (mul_eq_zero.mp this).resolve_right hlog

end General

section Prefix

variable {Ω : Type*} {k : ℕ} {α : Fin k → Type*} [∀ l, MeasurableSpace (α l)]
  (Z : ∀ l, Ω → α l)

lemma sourceSigma_mono {T T' : Finset (Fin k)} (h : T ⊆ T') : sourceSigma Z T ≤ sourceSigma Z T' :=
  iSup_mono' (fun j => ⟨j, iSup_mono' (fun hj => ⟨h hj, le_rfl⟩)⟩)

lemma sourceSigma_le {mΩ : MeasurableSpace Ω} (hZ : ∀ l, Measurable (Z l)) (T : Finset (Fin k)) :
    sourceSigma Z T ≤ mΩ :=
  iSup₂_le (fun l _ => (hZ l).comap_le)

lemma prefixSigma_mono {j j' : ℕ} (h : j ≤ j') : prefixSigma Z j ≤ prefixSigma Z j' :=
  sourceSigma_mono Z (fun l hl => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢; omega)

lemma prefixSigma_zero : prefixSigma Z 0 = ⊥ := by
  simp [prefixSigma, sourceSigma]

lemma prefixSigma_k : prefixSigma Z k = sourceSigma Z Finset.univ := by
  have : (Finset.univ.filter (fun l : Fin k => (l : ℕ) < k)) = Finset.univ := by
    ext l; simp
  simp only [prefixSigma, this]

end Prefix

section Main

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSingletonClass β]
  {k : ℕ} {α : Fin k → Type*} [∀ l, MeasurableSpace (α l)]
  (P : Measure Ω) [IsProbabilityMeasure P] (Z : ∀ l, Ω → α l) (hZ : ∀ l, Measurable (Z l))
  (X : Ω → β)

/-- Monotonicity of `f_X` on `ℕ`. -/
theorem infoCDF_mono_of_le (hZ : ∀ l, Measurable (Z l)) (hfin : (Set.range X).Finite)
    (hX : Measurable X) {j j' : ℕ} (h : j ≤ j') :
    infoCDF P Z X j ≤ infoCDF P Z X j' := by
  unfold infoCDF mutualInfo
  have := condEntropy_anti P X hfin hX (prefixSigma_mono Z h) (sourceSigma_le Z hZ _)
  linarith

theorem infoCDF_zero (hX : Measurable X) : infoCDF P Z X 0 = 0 := by
  unfold infoCDF mutualInfo
  rw [prefixSigma_zero, condEntropy_bot P X hX]; ring

theorem infoCDF_k (hZ : ∀ l, Measurable (Z l)) (hfin : (Set.range X).Finite)
    (hX : Measurable[sourceSigma Z Finset.univ] X) :
    infoCDF P Z X k = entropy P X := by
  unfold infoCDF mutualInfo
  rw [prefixSigma_k, condEntropy_of_measurable P X hfin (sourceSigma_le Z hZ _) hX]; ring

end Main

end EntropyLocalCoord.Dev.CDF

open MeasureTheory EntropyLocalCoord.Leader in
theorem EntropyLocalCoord.Leader.chk_infoCDF_mono {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [MeasurableSingletonClass β] {k : ℕ} {α : Fin k → Type*} [∀ l, MeasurableSpace (α l)]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ∀ l, Ω → α l) (hZ : ∀ l, Measurable (Z l))
    (X : Ω → β) (hfin : (Set.range X).Finite)
    (hX : Measurable[sourceSigma Z Finset.univ] X) :
    MonotoneOn (infoCDF P Z X) (Set.Iic k) ∧
      infoCDF P Z X 0 = 0 ∧
      infoCDF P Z X k = entropy P X ∧
      ∀ j ≤ k, infoCDF P Z X j ∈ Set.Icc 0 (entropy P X) := by
  have hXm : Measurable X := hX.mono (EntropyLocalCoord.Dev.CDF.sourceSigma_le Z hZ _) le_rfl
  have hmono := fun {j j' : ℕ} (h : j ≤ j') =>
    EntropyLocalCoord.Dev.CDF.infoCDF_mono_of_le P Z X hZ hfin hXm h
  have h0 := EntropyLocalCoord.Dev.CDF.infoCDF_zero P Z X hXm
  have hk := EntropyLocalCoord.Dev.CDF.infoCDF_k P Z X hZ hfin hX
  refine ⟨fun a _ b _ hab => hmono hab, h0, hk, fun j hj => ⟨?_, ?_⟩⟩
  · rw [← h0]; exact hmono (Nat.zero_le j)
  · rw [← hk]; exact hmono hj
end

theorem solution : type_of% @EntropyLocalCoord.Leader.chk_infoCDF_mono := @EntropyLocalCoord.Leader.chk_infoCDF_mono
