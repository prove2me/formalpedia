-- Prove2me | solution 1 for DistInterpRO.Shrinkage.two_scenario_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:46:29.528235+00:00
-- url     : https://prove2.me/submissions/71ccb50e-f63d-4fbe-8a73-5eb5da489fd6

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

theorem aux_tsv_lower {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : Continuous F)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ) (α : ℝ)
    (c : ℝ) (hc : ∀ y ∈ Δ, c ≤ F (x₀ + y))
    (μ : Measure (EuclideanSpace ℝ (Fin m))) (hμ : μ ∈ scenarioSet x₀ Δ (1 - α)) :
    Integrable F μ ∧ (1 - α) * F x₀ + α * c ≤ ∫ x, F x ∂μ := by
  obtain ⟨hprob, hx₀, hS⟩ := hμ
  have hScomp : IsCompact ((fun x => x₀ + x) '' Δ) :=
    hΔc.image (continuous_const.add continuous_id)
  have hSmeas : MeasurableSet ((fun x => x₀ + x) '' Δ) := hScomp.isClosed.measurableSet
  have hae : ∀ᵐ x ∂μ, x ∈ (fun x => x₀ + x) '' Δ := by
    exact mem_ae_iff.2 ((prob_compl_eq_zero_iff hSmeas).mpr hS)
  obtain ⟨C, hC⟩ := hScomp.exists_bound_of_continuousOn hF.continuousOn
  have hint : Integrable F μ := by
    refine Integrable.of_bound hF.aestronglyMeasurable C ?_
    filter_upwards [hae] with x hx using hC x hx
  refine ⟨hint, ?_⟩
  have hFx0 : c ≤ F x₀ := by simpa using hc 0 hΔ0
  let g : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun x => c + ({x₀} : Set (EuclideanSpace ℝ (Fin m))).indicator (fun _ => F x₀ - c) x
  have hind : Integrable
      (fun x => ({x₀} : Set (EuclideanSpace ℝ (Fin m))).indicator (fun _ => F x₀ - c) x) μ :=
    (integrable_const (F x₀ - c)).indicator (measurableSet_singleton x₀)
  have hgint : Integrable g μ := (integrable_const c).add hind
  have hgle : g ≤ᵐ[μ] F := by
    filter_upwards [hae] with x hx
    obtain ⟨y, hy, rfl⟩ := hx
    by_cases h : x₀ + y = x₀
    · simp only [g]
      rw [h, Set.indicator_of_mem (Set.mem_singleton x₀)]
      linarith
    · simp only [g]
      rw [Set.indicator_of_notMem (by simpa using h)]
      simpa using hc y hy
  have hgval : ∫ x, g x ∂μ = c + μ.real {x₀} * (F x₀ - c) := by
    simp only [g]
    rw [integral_add (integrable_const c) hind, integral_const,
      integral_indicator_const _ (measurableSet_singleton x₀)]
    simp
  have hreal : 1 - α ≤ μ.real {x₀} := by
    rw [Measure.real]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mp hx₀
  have hmono := integral_mono_ae hgint hint hgle
  rw [hgval] at hmono
  nlinarith [mul_nonneg (sub_nonneg.mpr hreal) (sub_nonneg.mpr hFx0)]

theorem aux_tsv_main {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : Continuous F)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (1 - α) * F x₀ + α * (⨅ x : Δ, F (x₀ + x)) = drspValue F x₀ Δ (1 - α) := by
  obtain ⟨d, hdΔ, hdmin⟩ := hΔc.exists_isMinOn ⟨0, hΔ0⟩
    ((hF.comp (continuous_const.add continuous_id)).continuousOn)
  have hlow : ∀ y ∈ Δ, F (x₀ + d) ≤ F (x₀ + y) := fun y hy => hdmin hy
  have : Nonempty Δ := ⟨⟨0, hΔ0⟩⟩
  have hc : (⨅ x : Δ, F (x₀ + x)) = F (x₀ + d) := by
    apply le_antisymm
    · refine ciInf_le ?_ (⟨d, hdΔ⟩ : Δ)
      refine ⟨F (x₀ + d), ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hlow x.1 x.2
    · exact le_ciInf (fun x => hlow x.1 x.2)
  rw [hc]
  have hsum : ENNReal.ofReal (1 - α) + ENNReal.ofReal α = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hα0.le]
    simp
  have hx0S : x₀ ∈ (fun x => x₀ + x) '' Δ := ⟨0, hΔ0, by simp⟩
  have hdS : x₀ + d ∈ (fun x => x₀ + x) '' Δ := ⟨d, hdΔ, rfl⟩
  let μs : Measure (EuclideanSpace ℝ (Fin m)) :=
    ENNReal.ofReal (1 - α) • Measure.dirac x₀ + ENNReal.ofReal α • Measure.dirac (x₀ + d)
  have hmem : μs ∈ scenarioSet x₀ Δ (1 - α) := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · simp only [μs, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      exact hsum
    · simp only [μs, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply_of_mem (Set.mem_singleton x₀), mul_one]
      exact le_self_add
    · simp only [μs, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply_of_mem hx0S, Measure.dirac_apply_of_mem hdS, mul_one]
      exact hsum
  have hintμs : Integrable F μs := (aux_tsv_lower F hF x₀ Δ hΔc hΔ0 α _ hlow μs hmem).1
  unfold drspValue
  apply le_antisymm
  · have : Nonempty (scenarioSet x₀ Δ (1 - α)) := ⟨⟨μs, hmem⟩⟩
    exact le_ciInf (fun μ => (aux_tsv_lower F hF x₀ Δ hΔc hΔ0 α _ hlow μ μ.2).2)
  · refine (ciInf_le ⟨(1 - α) * F x₀ + α * F (x₀ + d), ?_⟩ ⟨μs, hmem⟩).trans ?_
    · rintro _ ⟨μ, rfl⟩
      exact (aux_tsv_lower F hF x₀ Δ hΔc hΔ0 α _ hlow μ μ.2).2
    · show ∫ x, F x ∂μs ≤ _
      have h1 : Integrable F (ENNReal.ofReal (1 - α) • Measure.dirac x₀) :=
        hintμs.mono_measure (Measure.le_add_right le_rfl)
      have h2 : Integrable F (ENNReal.ofReal α • Measure.dirac (x₀ + d)) :=
        hintμs.mono_measure (Measure.le_add_left le_rfl)
      simp only [μs]
      rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
        integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by linarith),
        ENNReal.toReal_ofReal hα0.le, smul_eq_mul, smul_eq_mul]

end DistInterpRO.Shrinkage

open DistInterpRO.Shrinkage
open MeasureTheory
open scoped Pointwise

theorem solution {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (hf : Continuous (f v))
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) = drspValue (f v) x₀ Δ (1 - α) :=
  aux_tsv_main (f v) hf x₀ Δ hΔc hΔ0 α hα0 hα1
