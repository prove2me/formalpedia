-- Prove2me | solution 1 for ConvexRiskFn.Order.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T05:21:40.898789+00:00
-- url     : https://prove2.me/submissions/3e9bae5d-edc6-4877-909b-2a67efd9393a

import Mathlib
import Definitions.Def_ConvexRiskFn_Order_Setting
open MeasureTheory Set Filter
open scoped Topology
open ConvexRiskFn.Order

namespace RiskOrderQuantile
lemma cdfOf_eq_cdf_map {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    cdfOf P X = ProbabilityTheory.cdf (P.map X) := by
  let : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  funext t
  rw [ProbabilityTheory.cdf_eq_real, Measure.real, Measure.map_apply hX measurableSet_Iic]
  rfl

lemma level_nonempty (F : ℝ → ℝ) (h1 : Tendsto F atTop (𝓝 1))
    (t : ℝ) (ht : t < 1) : {s : ℝ | t ≤ F s}.Nonempty := by
  obtain ⟨s, hs⟩ := (h1.eventually (Ioi_mem_nhds ht)).exists
  exact ⟨s, hs.le⟩

lemma level_bddBelow (F : ℝ → ℝ) (hmono : Monotone F)
    (h0 : Tendsto F atBot (𝓝 0)) (t : ℝ) (ht : 0 < t) :
    BddBelow {s : ℝ | t ≤ F s} := by
  obtain ⟨s, hs⟩ := (h0.eventually (Iio_mem_nhds ht)).exists
  refine ⟨s, ?_⟩
  intro x hx
  by_contra hn
  have := hmono (le_of_lt (lt_of_not_ge hn))
  exact (not_le_of_gt hs) (hx.trans this)

lemma inverse_order (F₁ F₂ : ℝ → ℝ) (hmono : Monotone F₁)
    (h0 : Tendsto F₁ atBot (𝓝 0)) (h1 : Tendsto F₂ atTop (𝓝 1))
    (hF : ∀ s, F₂ s ≤ F₁ s) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    cdfInv F₁ t ≤ cdfInv F₂ t := by
  exact csInf_le_csInf (level_bddBelow F₁ hmono h0 t ht.1)
    (level_nonempty F₂ h1 t ht.2) (fun s hs => hs.trans (hF s))

lemma inverse_le_iff (F : StieltjesFunction ℝ)
    (h0 : Tendsto F atBot (𝓝 0)) (h1 : Tendsto F atTop (𝓝 1))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    cdfInv F t ≤ x ↔ t ≤ F x := by
  have hb := level_bddBelow F F.mono h0 t ht.1
  have hn := level_nonempty F h1 t ht.2
  constructor
  · intro hx
    rw [← F.iInf_Ioi_eq x]
    apply le_ciInf
    intro r
    obtain ⟨s, hs, hsr⟩ := (csInf_lt_iff hb hn).mp (lt_of_le_of_lt hx r.2)
    exact hs.trans (F.mono hsr.le)
  · intro hx
    exact csInf_le hb hx

lemma inverse_zero_of_nonpos (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x)
    (t : ℝ) (ht : t ≤ 0) : cdfInv F t = 0 := by
  have he : {s : ℝ | t ≤ F s} = univ := by
    ext s; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact ht.trans (hF s)
  rw [cdfInv, he, csInf_of_not_bddBelow (s := (univ : Set ℝ)) not_bddBelow_univ, Real.sInf_empty]

lemma inverse_zero_of_gt_one (F : ℝ → ℝ) (hF : ∀ x, F x ≤ 1)
    (t : ℝ) (ht : 1 < t) : cdfInv F t = 0 := by
  have he : {s : ℝ | t ≤ F s} = ∅ := by
    ext s; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_le.mpr (lt_of_le_of_lt (hF s) ht)
  rw [cdfInv, he, Real.sInf_empty]

lemma inverse_measurable (F : StieltjesFunction ℝ)
    (h0 : Tendsto F atBot (𝓝 0)) (h1 : Tendsto F atTop (𝓝 1))
    (hnonneg : ∀ x, 0 ≤ F x) (hone : ∀ x, F x ≤ 1) :
    Measurable (cdfInv F) := by
  apply measurable_of_Iic
  intro x
  have he : (cdfInv F) ⁻¹' Iic x =
      {t : ℝ | (0 < t ∧ t < 1 ∧ t ≤ F x) ∨
        (t ≤ 0 ∧ 0 ≤ x) ∨ (1 < t ∧ 0 ≤ x) ∨ (t = 1 ∧ cdfInv F 1 ≤ x)} := by
    ext t
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
    by_cases ht0 : t ≤ 0
    · rw [inverse_zero_of_nonpos F hnonneg t ht0]
      simp [ht0, not_lt.mpr ht0, show ¬1 < t by linarith, show t ≠ 1 by linarith]
    · by_cases ht1 : 1 < t
      · rw [inverse_zero_of_gt_one F hone t ht1]
        simp [ht0, ht1, not_lt.mpr ht1.le, ne_of_gt ht1]
      · by_cases ht : t = 1
        · subst t; simp
        · have hi : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_not_ge ht0, lt_of_le_of_ne (le_of_not_gt ht1) ht⟩
          rw [inverse_le_iff F h0 h1 t hi x]
          simp [hi.1, hi.2, ht0, ht1, ht]
  rw [he]
  measurability

lemma uniform_map {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → ℝ) (hU : IsUniformRV P U) :
    P.map U = volume.restrict (Icc (0 : ℝ) 1) := by
  let : IsProbabilityMeasure (P.map U) := Measure.isProbabilityMeasure_map hU.1.aemeasurable
  let : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hU.1 measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  by_cases ht0 : t < 0
  · have hzero := hU.2 0 (by simp)
    have hsub : {ω | U ω ≤ t} ⊆ {ω | U ω ≤ 0} := fun ω hω => hω.trans ht0.le
    have he : Iic t ∩ Icc (0 : ℝ) 1 = ∅ := by ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]; intro hx; linarith [hx.1,hx.2.1]
    change P {ω | U ω ≤ t} = _
    rw [he, measure_empty]
    apply le_antisymm ?_ zero_le
    simpa only [hzero, ENNReal.ofReal_zero] using (measure_mono (μ := P) hsub)
  · by_cases ht1 : t ≤ 1
    · have he : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨hxt, hx0, _⟩; exact ⟨hx0, hxt⟩
        · rintro ⟨hx0, hxt⟩; exact ⟨hxt, hx0, hxt.trans ht1⟩
      change P {ω | U ω ≤ t} = _
      rw [hU.2 t ⟨le_of_not_gt ht0, ht1⟩, he, Real.volume_Icc, sub_zero]
    · have hsub : {ω | U ω ≤ 1} ⊆ {ω | U ω ≤ t} := fun ω hω => hω.trans (le_of_not_ge ht1)
      have he : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
        apply inter_eq_right.mpr
        intro x hx; exact hx.2.trans (le_of_not_ge ht1)
      change P {ω | U ω ≤ t} = _
      rw [he]; simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
      apply le_antisymm (prob_le_one) ?_
      simpa only [hU.2 1 (by simp), ENNReal.ofReal_one] using (measure_mono (μ := P) hsub)

lemma uniform_ae_interior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → ℝ) (hU : IsUniformRV P U) :
    ∀ᵐ ω ∂P, U ω ∈ Ioo (0 : ℝ) 1 := by
  apply ae_of_ae_map hU.1.aemeasurable
  rw [uniform_map P U hU]
  filter_upwards [ae_restrict_mem measurableSet_Icc, Measure.ae_ne (volume.restrict (Icc (0 : ℝ) 1)) 0, Measure.ae_ne (volume.restrict (Icc (0 : ℝ) 1)) 1] with x hx hx0 hx1
  exact ⟨lt_of_le_of_ne hx.1 hx0.symm, lt_of_le_of_ne hx.2 hx1⟩

end RiskOrderQuantile

open ProbabilityTheory RiskOrderQuantile
namespace RiskOrderStochastic
lemma quantile_identDistrib {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → ℝ) (hU : IsUniformRV P U)
    (Q : Measure Ω') [IsProbabilityMeasure Q] (X : Ω' → ℝ) (hX : Measurable X) :
    IdentDistrib (fun ω => cdfInv (cdfOf Q X) (U ω)) X P Q := by
  let : IsProbabilityMeasure (Q.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hc := cdfOf_eq_cdf_map Q X hX
  have hq : Measurable (fun ω => cdfInv (cdfOf Q X) (U ω)) := by
    rw [hc]
    exact (inverse_measurable (cdf (Q.map X)) (tendsto_cdf_atBot _) (tendsto_cdf_atTop _)
      (cdf_nonneg _) (cdf_le_one _)).comp hU.1
  refine ⟨hq.aemeasurable, hX.aemeasurable, ?_⟩
  let : IsProbabilityMeasure (P.map (fun ω => cdfInv (cdfOf Q X) (U ω))) :=
    Measure.isProbabilityMeasure_map hq.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hq measurableSet_Iic, Measure.map_apply hX measurableSet_Iic]
  change P {ω | cdfInv (cdfOf Q X) (U ω) ≤ t} = Q {ω | X ω ≤ t}
  rw [hc]
  calc
    P {ω | cdfInv (cdf (Q.map X)) (U ω) ≤ t} = P {ω | U ω ≤ cdf (Q.map X) t} := by
      apply measure_congr
      filter_upwards [uniform_ae_interior P U hU] with ω hω
      exact propext (inverse_le_iff _ (tendsto_cdf_atBot _) (tendsto_cdf_atTop _) _ hω t)
    _ = ENNReal.ofReal (cdf (Q.map X) t) := hU.2 _ ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
    _ = Q {ω | X ω ≤ t} := by
      rw [ofReal_cdf, Measure.map_apply hX measurableSet_Iic]; rfl

lemma canonical_uniform : IsUniformRV (volume.restrict (Icc (0 : ℝ) 1)) id := by
  refine ⟨measurable_id, ?_⟩
  intro t ht
  change (volume.restrict (Icc (0 : ℝ) 1)) (Iic t) = ENNReal.ofReal t
  rw [Measure.restrict_apply measurableSet_Iic]
  have he : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
    ext x; simp only [mem_Iic, mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨hxt, hx0, _⟩; exact ⟨hx0, hxt⟩
    · rintro ⟨hx0, hxt⟩; exact ⟨hxt, hx0, hxt.trans ht.2⟩
  rw [he, Real.volume_Icc, sub_zero]

lemma st_implies_cdf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₁ X₂ : Ω → ℝ)
    (h₁ : Measurable X₁) (h₂ : Measurable X₂) (h : StLE P X₁ X₂) :
    ∀ t, P {ω | X₂ ω ≤ t} ≤ P {ω | X₁ ω ≤ t} := by
  intro t
  let u : ℝ → ℝ := (Iic t).indicator (fun _ => -1)
  have hu : Monotone u := by
    intro a b hab
    simp only [u, indicator_apply, mem_Iic]
    split_ifs <;> linarith
  have hi (X : Ω → ℝ) (hX : Measurable X) : Integrable (u ∘ X) P := by
    change Integrable ((X ⁻¹' Iic t).indicator (fun _ => (-1 : ℝ))) P
    exact (integrable_const (-1 : ℝ)).indicator (hX measurableSet_Iic)
  have hv (X : Ω → ℝ) (hX : Measurable X) :
      (∫ ω, u (X ω) ∂P) = -(P {ω | X ω ≤ t}).toReal := by
    have := integral_indicator_const (μ := P) (s := X ⁻¹' Iic t) (-1 : ℝ) (hX measurableSet_Iic)
    change (∫ ω, (X ⁻¹' Iic t).indicator (fun _ => (-1 : ℝ)) ω ∂P) =
      -(P (X ⁻¹' Iic t)).toReal
    simpa [Measure.real, smul_eq_mul] using this
  have hh := h u hu (hi X₁ h₁) (hi X₂ h₂)
  rw [hv X₁ h₁, hv X₂ h₂] at hh
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (by linarith)

lemma cdf_implies_st {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₁ X₂ : Ω → ℝ)
    (h₁ : Measurable X₁) (h₂ : Measurable X₂)
    (hF : ∀ t, P {ω | X₂ ω ≤ t} ≤ P {ω | X₁ ω ≤ t}) : StLE P X₁ X₂ := by
  let Q : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure Q := ⟨by simp [Q]⟩
  have hd₁ := quantile_identDistrib Q id canonical_uniform P X₁ h₁
  have hd₂ := quantile_identDistrib Q id canonical_uniform P X₂ h₂
  have hcf : ∀ t, cdfOf P X₂ t ≤ cdfOf P X₁ t := fun t => ENNReal.toReal_mono (measure_ne_top _ _) (hF t)
  let : IsProbabilityMeasure (P.map X₁) := Measure.isProbabilityMeasure_map h₁.aemeasurable
  let : IsProbabilityMeasure (P.map X₂) := Measure.isProbabilityMeasure_map h₂.aemeasurable
  have hord : ∀ᵐ t ∂Q, cdfInv (cdfOf P X₁) t ≤ cdfInv (cdfOf P X₂) t := by
    filter_upwards [uniform_ae_interior Q id canonical_uniform] with t ht
    rw [cdfOf_eq_cdf_map P X₁ h₁, cdfOf_eq_cdf_map P X₂ h₂]
    rw [cdfOf_eq_cdf_map P X₁ h₁, cdfOf_eq_cdf_map P X₂ h₂] at hcf
    exact inverse_order _ _ (monotone_cdf _) (tendsto_cdf_atBot _) (tendsto_cdf_atTop _) hcf t ht
  intro u hu hi₁ hi₂
  have hdu₁ := hd₁.comp hu.measurable
  have hdu₂ := hd₂.comp hu.measurable
  calc
    (∫ ω, u (X₁ ω) ∂P) = ∫ t, u (cdfInv (cdfOf P X₁) t) ∂Q := hdu₁.integral_eq.symm
    _ ≤ ∫ t, u (cdfInv (cdfOf P X₂) t) ∂Q := by
      apply integral_mono_ae (hdu₁.integrable_iff.mpr hi₁) (hdu₂.integrable_iff.mpr hi₂)
      filter_upwards [hord] with t ht using hu ht
    _ = ∫ ω, u (X₂ ω) ∂P := hdu₂.integral_eq
end RiskOrderStochastic

open RiskOrderStochastic

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hU : ∃ U : Ω → ℝ, IsUniformRV P U)
    (ρ : (Ω → ℝ) → ℝ) (hρ : DistInvariant P p ρ) :
    ConsistentSt P p ρ ↔ A2 P p ρ := by
  constructor
  · intro h X Y hX hY hxy
    apply h X Y hX hY
    intro u hu hiX hiY
    apply integral_mono_ae hiX hiY
    filter_upwards [hxy] with ω hω using hu hω
  · intro h X Y hX hY hst
    obtain ⟨U, hU⟩ := hU
    let X' := hX.aestronglyMeasurable.mk X
    let Y' := hY.aestronglyMeasurable.mk Y
    have hmX : Measurable X' := hX.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hmY : Measurable Y' := hY.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have haX : X =ᵐ[P] X' := hX.aestronglyMeasurable.ae_eq_mk
    have haY : Y =ᵐ[P] Y' := hY.aestronglyMeasurable.ae_eq_mk
    have hidX : IdentDistrib X' X P P :=
      ⟨hmX.aemeasurable, hX.aestronglyMeasurable.aemeasurable, Measure.map_congr haX.symm⟩
    have hidY : IdentDistrib Y' Y P P :=
      ⟨hmY.aemeasurable, hY.aestronglyMeasurable.aemeasurable, Measure.map_congr haY.symm⟩
    have hs' : StLE P X' Y' := by
      intro u hu hiX hiY
      have hduX := hidX.comp hu.measurable
      have hduY := hidY.comp hu.measurable
      change (∫ ω, (u ∘ X') ω ∂P) ≤ ∫ ω, (u ∘ Y') ω ∂P
      rw [hduX.integral_eq, hduY.integral_eq]
      exact hst u hu (hduX.integrable_iff.mp hiX) (hduY.integrable_iff.mp hiY)
    let qX : Ω → ℝ := fun ω => cdfInv (cdfOf P X') (U ω)
    let qY : Ω → ℝ := fun ω => cdfInv (cdfOf P Y') (U ω)
    have hdX := (quantile_identDistrib P U hU P X' hmX).trans hidX
    have hdY := (quantile_identDistrib P U hU P Y' hmY).trans hidY
    have hqX : MemLp qX p P := hdX.memLp_iff.mpr hX
    have hqY : MemLp qY p P := hdY.memLp_iff.mpr hY
    have hcdf := st_implies_cdf P X' Y' hmX hmY hs'
    have hcf : ∀ t, cdfOf P Y' t ≤ cdfOf P X' t :=
      fun t => ENNReal.toReal_mono (measure_ne_top _ _) (hcdf t)
    let : IsProbabilityMeasure (P.map X') := Measure.isProbabilityMeasure_map hmX.aemeasurable
    let : IsProbabilityMeasure (P.map Y') := Measure.isProbabilityMeasure_map hmY.aemeasurable
    have hq : qX ≤ᵐ[P] qY := by
      filter_upwards [uniform_ae_interior P U hU] with ω hω
      change cdfInv (cdfOf P X') (U ω) ≤ cdfInv (cdfOf P Y') (U ω)
      rw [cdfOf_eq_cdf_map P X' hmX, cdfOf_eq_cdf_map P Y' hmY]
      rw [cdfOf_eq_cdf_map P X' hmX, cdfOf_eq_cdf_map P Y' hmY] at hcf
      exact inverse_order _ _ (monotone_cdf _) (tendsto_cdf_atBot _) (tendsto_cdf_atTop _) hcf _ hω
    have hrX : ρ qX = ρ X := hρ qX X hqX hX (fun t => hdX.measure_mem_eq measurableSet_Iic)
    have hrY : ρ qY = ρ Y := hρ qY Y hqY hY (fun t => hdY.measure_mem_eq measurableSet_Iic)
    rw [← hrX, ← hrY]
    exact h qX qY hqX hqY hq

#print axioms solution

open MeasureTheory
namespace ConvexRiskFn.Order

/-- Lemma 5.1, p. 445: under the standing assumptions of §5.2 (`𝒳 = ℒ_p(Ω, ℱ, P)`, `p ∈ [1, ∞)`,
a uniform random variable exists), a distribution-invariant risk function is consistent with the
usual stochastic order iff it satisfies (A2). -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hU : ∃ U : Ω → ℝ, IsUniformRV P U)
    (ρ : (Ω → ℝ) → ℝ) (hρ : DistInvariant P p ρ) :
    ConsistentSt P p ρ ↔ A2 P p ρ := by
  exact solution P p hp1 hpt hU ρ hρ

end ConvexRiskFn.Order

#print axioms solution
