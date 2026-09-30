-- Prove2me | solution 1 for DRCVRP.RCI.chance_constraint_iff_worstCaseVaR_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:08:44.415364+00:00
-- url     : https://prove2.me/submissions/96c68a07-6e2c-4a8f-b05f-5cb29539478f

import Definitions.Def_DRCVRP_RCI_Formulations
import Definitions.Def_MultistageStochastic_RiskFunctional
import Mathlib.Probability.CDF
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
private theorem var_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (τ : ℝ) :
    ENNReal.ofReal α ≤ P {q | X q ≤ τ} ↔ MultistageStochastic.valueAtRisk P X α ≤ τ := by
  haveI : IsProbabilityMeasure (P.map X) := P.isProbabilityMeasure_map hX.aemeasurable
  let F := cdf (P.map X)
  have hf (y : ℝ) : ENNReal.ofReal α ≤ P {q | X q ≤ y} ↔ α ≤ F y := by
    change ENNReal.ofReal α ≤ P (X ⁻¹' Iic y) ↔ α ≤ F y
    rw [← Measure.map_apply hX measurableSet_Iic, ← ofReal_cdf]
    exact ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)
  have heq : {y : ℝ | ENNReal.ofReal α ≤ P {q | X q ≤ y}} = {y : ℝ | α ≤ F y} := by
    ext y
    exact hf y
  let S := {y : ℝ | α ≤ F y}
  have hne : S.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop (P.map X)).eventually (eventually_gt_nhds hα1)).exists
    exact ⟨y, hy.le⟩
  have hb : BddBelow S := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atBot (P.map X)).eventually (eventually_lt_nhds hα0)).exists
    refine ⟨y, fun z hz => ?_⟩
    by_contra h
    have hzy : z ≤ y := le_of_not_ge h
    have hh := F.mono hzy
    exact (not_lt_of_ge (hz.trans hh)) hy
  have hmem : α ≤ F (sInf S) := by
    have hlim : Tendsto F (𝓝[>] sInf S) (𝓝 (F (sInf S))) :=
      (F.right_continuous _).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
    exact hz.trans (F.mono hzy.le)
  rw [hf, MultistageStochastic.valueAtRisk, heq]
  exact ⟨fun h => csInf_le hb h, fun h => hmem.trans (F.mono h)⟩

open DRCVRP.RCI
theorem solution {n : ℕ} (Amb : Set (Measure (Fin n → ℝ)))
    (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P) (hne : Amb.Nonempty)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (Q : ℝ) (r : List (Fin n)) (hr : r.Nodup)
    (hbdd : BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ r.toFinset, q i) (1 - ε)) '' Amb)) :
    (RouteChanceFeasible Amb ε Q r ↔
      ∀ P ∈ Amb, MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ r.toFinset, q i) (1 - ε) ≤ Q) ∧
    (RouteChanceFeasible Amb ε Q r ↔ worstCaseVaR Amb ε r.toFinset ≤ Q) := by
  have heq (q : Fin n → ℝ) : (r.map q).sum = ∑ i ∈ r.toFinset, q i := by
    exact (List.sum_toFinset _ hr).symm
  have hfirst : RouteChanceFeasible Amb ε Q r ↔
      ∀ P ∈ Amb, MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ r.toFinset, q i) (1-ε) ≤ Q := by
    unfold RouteChanceFeasible
    simp only [heq]
    apply forall₂_congr
    intro P hP
    haveI := hAmb P hP
    exact var_iff P _ (by fun_prop) (1-ε) (by linarith) (by linarith) Q
  refine ⟨hfirst, hfirst.trans ?_⟩
  unfold worstCaseVaR
  constructor
  · intro h
    apply csSup_le (hne.image _)
    rintro y ⟨P,hP,rfl⟩
    exact h P hP
  · intro h P hP
    exact (le_csSup hbdd ⟨P,hP,rfl⟩).trans h
