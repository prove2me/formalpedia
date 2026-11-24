-- Prove2me | solution 1 for BalanceSpecification.isClosed_setOf_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:20.402189+00:00
-- url     : https://prove2.me/submissions/5b1c7e54-d3d7-47e1-89f0-3d1acd6f881c

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Theorems.Thm_BalanceSpecification_continuous_shiftMap
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurable_shiftMap
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) :
    IsClosed {μ : ProbabilityMeasure X.carrier | IsInvariant μ} := by
  rw [isClosed_iff_forall_filter]
  intro μ l hl hle hlim
  have : l.NeBot := hl
  have hfin : (μ.map (continuous_shiftMap X).aemeasurable).toFiniteMeasure = μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro g
    change ∫ y, g y ∂((μ : Measure X.carrier).map (shiftMap X)) = ∫ y, g y ∂(μ : Measure X.carrier)
    rw [integral_map (continuous_shiftMap X).aemeasurable g.continuous.aestronglyMeasurable]
    let gf : BoundedContinuousFunction X.carrier ℝ :=
      BoundedContinuousFunction.mkOfBound ⟨g ∘ shiftMap X, g.continuous.comp (continuous_shiftMap X)⟩ (2 * ‖g‖) fun y₁ y₂ => by
        calc dist (g (shiftMap X y₁)) (g (shiftMap X y₂))
            ≤ dist (g (shiftMap X y₁)) 0 + dist 0 (g (shiftMap X y₂)) := dist_triangle _ 0 _
          _ = ‖g (shiftMap X y₁)‖ + ‖g (shiftMap X y₂)‖ := by rw [dist_zero_right, dist_zero_left]
          _ ≤ ‖g‖ + ‖g‖ := add_le_add (g.norm_coe_le_norm _) (g.norm_coe_le_norm _)
          _ = 2 * ‖g‖ := by ring
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) gf
    have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) g
    have hev : ∀ᶠ (ν : ProbabilityMeasure X.carrier) in l, (∫ y, gf y ∂(ν : Measure X.carrier)) = ∫ y, g y ∂(ν : Measure X.carrier) := by
      refine Filter.mem_of_superset (hle (Filter.mem_principal_self _)) ?_
      intro ν hν
      have hmap := integral_map (continuous_shiftMap X).aemeasurable g.continuous.aestronglyMeasurable (μ := (ν : Measure X.carrier))
      simpa [gf, hν.map_eq] using hmap.symm
    exact tendsto_nhds_unique (h1.congr' hev) h2
  exact ⟨measurable_shiftMap X, congrArg (fun ν : FiniteMeasure X.carrier => (ν : Measure X.carrier)) hfin⟩
end BalanceSpecification
