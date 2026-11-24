-- Prove2me | solution 1 for BalanceSpecification.measurePreserving_of_mapClusterPt_finiteOrbitProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:59.62454+00:00
-- url     : https://prove2.me/submissions/d77bef19-d01e-4bf6-a507-b17518adea33

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_tendsto_integral_comp_sub_finiteOrbitProbability

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [T2Space Ω]
    [HasOuterApproxClosed Ω]
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
namespace BalanceSpecification
theorem _root_.solution
    {f : Ω → Ω} (hf : Continuous f) (x : ∀ n, I n → Ω)
    {μ : ProbabilityMeasure Ω}
    (hμ : MapClusterPt μ atTop (fun n => finiteOrbitProbability f (x n) n)) :
    MeasurePreserving f (μ : Measure Ω) (μ : Measure Ω) := by
  have hfin : (μ.map hf.aemeasurable).toFiniteMeasure = μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro g
    change ∫ y, g y ∂((μ : Measure Ω).map f) = ∫ y, g y ∂(μ : Measure Ω)
    rw [integral_map hf.aemeasurable g.continuous.aestronglyMeasurable]
    obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hμ
    let gf : Ω →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfBound ⟨g ∘ f, g.continuous.comp hf⟩ (2 * ‖g‖) fun y₁ y₂ => by
        calc dist (g (f y₁)) (g (f y₂))
            ≤ dist (g (f y₁)) 0 + dist 0 (g (f y₂)) := dist_triangle _ 0 _
          _ = ‖g (f y₁)‖ + ‖g (f y₂)‖ := by rw [dist_zero_right, dist_zero_left]
          _ ≤ ‖g‖ + ‖g‖ := add_le_add (g.norm_coe_le_norm (f y₁)) (g.norm_coe_le_norm (f y₂))
          _ = 2 * ‖g‖ := by ring
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) gf
    have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) g
    have hsub := h1.sub h2
    have hzero : Tendsto (fun n =>
        (∫ y, (g ∘ f) y ∂(finiteOrbitProbability f (x n) n : Measure Ω)) -
          ∫ y, g y ∂(finiteOrbitProbability f (x n) n : Measure Ω)) U (𝓝 0) :=
      (tendsto_integral_comp_sub_finiteOrbitProbability f x g).mono_left hU
    exact sub_eq_zero.mp (tendsto_nhds_unique hsub hzero)
  exact ⟨hf.measurable, congrArg (fun ν : FiniteMeasure Ω => (ν : Measure Ω)) hfin⟩
end BalanceSpecification
