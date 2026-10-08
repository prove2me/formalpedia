-- Prove2me | solution 1 for DataDrivenRO.Marginal.var_le_sum_coord
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:45:33.955812+00:00
-- url     : https://prove2.me/submissions/29e7ac77-ee8e-4a18-af6e-137a977671a7

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- `{y | ofReal α ≤ P{Z ≤ y}}` written through the cdf of the law of `Z`. -/
theorem vle_set_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (α : ℝ) :
    {y : ℝ | ENNReal.ofReal α ≤ P {ω | Z ω ≤ y}} = {y | α ≤ cdf (P.map Z) y} := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  ext y
  simp only [mem_ofPred_eq]
  have h1 : P {ω | Z ω ≤ y} = ENNReal.ofReal (cdf (P.map Z) y) := by
    rw [ofReal_cdf, Measure.map_apply hZ measurableSet_Iic]; rfl
  rw [h1, ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)]

theorem vle_bdd (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf μ x} := by
  have h := (tendsto_cdf_atBot μ).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

theorem vle_nonempty (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf μ x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

theorem vle_attain (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf μ (sInf {x | u ≤ cdf μ x}) := by
  have hcont : ContinuousWithinAt (cdf μ) (Ici (sInf {x | u ≤ cdf μ x}))
      (sInf {x | u ≤ cdf μ x}) := (cdf μ).right_continuous _
  have ht : Tendsto (cdf μ) (𝓝[>] (sInf {x | u ≤ cdf μ x}))
      (𝓝 (cdf μ (sInf {x | u ≤ cdf μ x}))) := hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (vle_nonempty μ hu1) hx
  exact le_trans hs (monotone_cdf μ hsx.le)

/-- The VaR level set is attained: `α ≤ P.real {Z ≤ valueAtRisk P Z α}` for `α < 1`. -/
theorem vle_attain_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) {α : ℝ} (hα1 : α < 1) :
    α ≤ P.real {ω | Z ω ≤ MultistageStochastic.valueAtRisk P Z α} := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  unfold MultistageStochastic.valueAtRisk
  rw [vle_set_eq P Z hZ α]
  have h := vle_attain (P.map Z) hα1
  have h1 : P {ω | Z ω ≤ sInf {x | α ≤ cdf (P.map Z) x}}
      = ENNReal.ofReal (cdf (P.map Z) (sInf {x | α ≤ cdf (P.map Z) x})) := by
    rw [ofReal_cdf, Measure.map_apply hZ measurableSet_Iic]; rfl
  rw [measureReal_def, h1, ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  exact h

theorem vle_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) {α : ℝ} (hα0 : 0 < α) (t : ℝ)
    (ht : α ≤ P.real {ω | Z ω ≤ t}) :
    MultistageStochastic.valueAtRisk P Z α ≤ t := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  unfold MultistageStochastic.valueAtRisk
  rw [vle_set_eq P Z hZ α]
  refine csInf_le (vle_bdd (P.map Z) hα0) ?_
  have h1 : P {ω | Z ω ≤ t} = ENNReal.ofReal (cdf (P.map Z) t) := by
    rw [ofReal_cdf, Measure.map_apply hZ measurableSet_Iic]; rfl
  rw [measureReal_def, h1, ENNReal.toReal_ofReal (cdf_nonneg _ _)] at ht
  exact ht

open MeasureTheory DataDrivenRO.Marginal in
theorem solution {d : ℕ} (hd : 0 < d) (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) :
    VaR P ε v ≤ ∑ i, VaR P (ε / d) (Pi.single i (v i)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdge : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hεd0 : 0 < ε / d := div_pos hε0 hdpos
  have hεd1 : ε / d < 1 := by
    rw [div_lt_one hdpos]; linarith
  set Zi : Fin d → (Fin d → ℝ) → ℝ := fun i u => u ⬝ᵥ Pi.single i (v i) with hZi
  have hZim : ∀ i, Measurable (Zi i) := fun i =>
    (Continuous.dotProduct continuous_id continuous_const).measurable
  have hZm : Measurable (fun u : Fin d → ℝ => u ⬝ᵥ v) :=
    (Continuous.dotProduct continuous_id continuous_const).measurable
  set t : Fin d → ℝ := fun i => VaR P (ε / d) (Pi.single i (v i)) with ht
  have hA : ∀ i, 1 - ε / d ≤ P.real {u | Zi i u ≤ t i} := fun i =>
    vle_attain_real P (Zi i) (hZim i) (by linarith)
  have hsum : ∀ u : Fin d → ℝ, u ⬝ᵥ v = ∑ i, Zi i u := by
    intro u
    simp only [hZi, dotProduct_single]
    rfl
  -- complement bound
  have hsub : {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i}ᶜ ⊆ ⋃ i, {u | Zi i u ≤ t i}ᶜ := by
    intro u hu
    simp only [mem_compl_iff, mem_ofPred_eq, mem_iUnion] at hu ⊢
    by_contra hcon
    push Not at hcon
    apply hu
    rw [hsum u]
    exact Finset.sum_le_sum fun i _ => hcon i
  have hmB : MeasurableSet {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i} :=
    measurableSet_le hZm measurable_const
  have hmA : ∀ i, MeasurableSet {u : Fin d → ℝ | Zi i u ≤ t i} := fun i =>
    measurableSet_le (hZim i) measurable_const
  have hcB : P.real {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i}ᶜ ≤ ε := by
    calc P.real {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i}ᶜ
        ≤ P.real (⋃ i, {u | Zi i u ≤ t i}ᶜ) := measureReal_mono hsub
      _ ≤ ∑ i, P.real {u | Zi i u ≤ t i}ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin d, ε / d := by
          apply Finset.sum_le_sum
          intro i _
          rw [probReal_compl_eq_one_sub (hmA i)]
          linarith [hA i]
      _ = ε := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hB : 1 - ε ≤ P.real {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i} := by
    rw [probReal_compl_eq_one_sub hmB] at hcB
    linarith
  exact vle_le P (fun u => u ⬝ᵥ v) hZm (by linarith) _ hB
