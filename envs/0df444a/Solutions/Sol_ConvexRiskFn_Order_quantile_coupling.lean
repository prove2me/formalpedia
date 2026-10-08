-- Prove2me | solution 1 for ConvexRiskFn.Order.quantile_coupling
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T05:15:27.384497+00:00
-- url     : https://prove2.me/submissions/093edd81-92dc-4833-a9c6-723078d174e4

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

open RiskOrderQuantile ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : IsUniformRV P U) :
    (∀ X : Ω → ℝ, Measurable X →
        Measurable (fun ω => cdfInv (cdfOf P X) (U ω)) ∧
        ∀ t : ℝ, P {ω | cdfInv (cdfOf P X) (U ω) ≤ t} = P {ω | X ω ≤ t}) ∧
    (∀ X₁ X₂ : Ω → ℝ, Measurable X₁ → Measurable X₂ →
        (∀ t : ℝ, cdfOf P X₂ t ≤ cdfOf P X₁ t) →
        ∀ᵐ ω ∂P, cdfInv (cdfOf P X₁) (U ω) ≤ cdfInv (cdfOf P X₂) (U ω)) := by
  have hUi := uniform_ae_interior P U hU
  constructor
  · intro X hX
    let : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
    rw [cdfOf_eq_cdf_map P X hX]
    refine ⟨(inverse_measurable (cdf (P.map X)) (tendsto_cdf_atBot _)
      (tendsto_cdf_atTop _) (cdf_nonneg _) (cdf_le_one _)).comp hU.1, ?_⟩
    intro t
    calc
      P {ω | cdfInv (cdf (P.map X)) (U ω) ≤ t} = P {ω | U ω ≤ cdf (P.map X) t} := by
        apply measure_congr
        filter_upwards [hUi] with ω hω
        exact propext (inverse_le_iff _ (tendsto_cdf_atBot _) (tendsto_cdf_atTop _) _ hω t)
      _ = ENNReal.ofReal (cdf (P.map X) t) := hU.2 _ ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
      _ = P {ω | X ω ≤ t} := by
        rw [ofReal_cdf, Measure.map_apply hX measurableSet_Iic]; rfl
  · intro X₁ X₂ hX₁ hX₂ hF
    let : IsProbabilityMeasure (P.map X₁) := Measure.isProbabilityMeasure_map hX₁.aemeasurable
    let : IsProbabilityMeasure (P.map X₂) := Measure.isProbabilityMeasure_map hX₂.aemeasurable
    rw [cdfOf_eq_cdf_map P X₁ hX₁, cdfOf_eq_cdf_map P X₂ hX₂] at hF ⊢
    filter_upwards [hUi] with ω hω
    exact inverse_order _ _ (monotone_cdf _) (tendsto_cdf_atBot _) (tendsto_cdf_atTop _) hF _ hω

#print axioms solution

open MeasureTheory
namespace ConvexRiskFn.Order

/-- Proof of Lemma 5.1, p. 446: for a uniform random variable `U`, `X̂ := F_X⁻¹(U)` is a random
variable with the distribution of `X`, and `F_{X₂} ≤ F_{X₁}` gives `F_{X₁}⁻¹(U) ≤ F_{X₂}⁻¹(U)`
(almost surely: `U ∈ (0, 1)` only almost surely). -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : IsUniformRV P U) :
    (∀ X : Ω → ℝ, Measurable X →
        Measurable (fun ω => cdfInv (cdfOf P X) (U ω)) ∧
        ∀ t : ℝ, P {ω | cdfInv (cdfOf P X) (U ω) ≤ t} = P {ω | X ω ≤ t}) ∧
    (∀ X₁ X₂ : Ω → ℝ, Measurable X₁ → Measurable X₂ →
        (∀ t : ℝ, cdfOf P X₂ t ≤ cdfOf P X₁ t) →
        ∀ᵐ ω ∂P, cdfInv (cdfOf P X₁) (U ω) ≤ cdfInv (cdfOf P X₂) (U ω)) := by
  exact solution P U hU

end ConvexRiskFn.Order

#print axioms solution
