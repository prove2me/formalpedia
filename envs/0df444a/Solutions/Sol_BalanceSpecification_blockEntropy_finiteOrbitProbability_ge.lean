-- Prove2me | solution 1 for BalanceSpecification.blockEntropy_finiteOrbitProbability_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:07.342317+00:00
-- url     : https://prove2.me/submissions/b0a4193d-019d-4a26-b760-7e4e01dd0e6b

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_map_finitePointProbability
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_average_shannon_le
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_finiteOrbitProbability_real_apply
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
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
theorem _root_.solution {I : Type*} [Fintype I] [Nonempty I]
    (x : I → X.carrier) (N n : ℕ) :
    ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (N + 1),
      blockEntropy (translatedProbability (finitePointProbability x) j.val) n ≤
      blockEntropy (finiteOrbitProbability (shiftMap X) x N) n := by
  have hd : (fun w : ↥(wordFinset (language X) n) =>
      ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (N + 1),
        blockDistribution (translatedProbability (finitePointProbability x) j.val) n w) =
      blockDistribution (finiteOrbitProbability (shiftMap X) x N) n := by
    funext w
    have he := finiteOrbitProbability_real_apply (shiftMap X) x N (measurableSet_cylinder X w.val 0)
    simp only [translatedProbability, map_finitePointProbability x ((measurable_shiftMap X).iterate _)]
    exact he.symm
  have h := FiniteEntropy.average_shannon_le
    (p := fun j : Fin (N + 1) => blockDistribution
      (translatedProbability (finitePointProbability x) j.val) n)
    (fun _ _ => measureReal_nonneg)
  simp only [Fintype.card_fin] at h
  rw [hd, ← blockEntropy_eq_shannon] at h
  simpa only [← blockEntropy_eq_shannon, Fintype.card_fin] using h
end BalanceSpecification
