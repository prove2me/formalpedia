-- Prove2me | solution 1 for BalanceSpecification.exists_near_pure_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:52.58755+00:00
-- url     : https://prove2.me/submissions/9b830e26-899f-40e6-a093-cf5fe0ca2fd7

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_disjoint_cylinder
public import Theorems.Thm_BalanceSpecification_exists_centered_cylinder_approximation_real
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_mem_allWords
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
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    (μ : Measure X.carrier) [IsFiniteMeasure μ] {B : Set X.carrier}
    (hB : MeasurableSet B) (hBpos : 0 < μ.real B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w ∈ language X, ∃ k : ℤ,
      0 < μ.real (cylinder X w k) ∧
      (1 - δ) * μ.real (cylinder X w k) < μ.real (B ∩ cylinder X w k) := by
  classical
  let ε := min (μ.real B / 2) (δ * μ.real B / 2)
  have hε : 0 < ε := lt_min (half_pos hBpos) (half_pos (mul_pos hδ hBpos))
  obtain ⟨n, S, hS, herr⟩ := exists_centered_cylinder_approximation_real μ hB hε
  let E := ⋃ w ∈ S, cylinder X w (-(n : ℤ))
  have hE : MeasurableSet E := S.measurableSet_biUnion (fun w _ => measurableSet_cylinder X w _)
  have herr1 : μ.real (B ∆ E) < μ.real B / 2 := herr.trans_le (min_le_left _ _)
  have herr2 : μ.real (B ∆ E) < δ * μ.real B / 2 := herr.trans_le (min_le_right _ _)
  have hBEerr : μ.real (B \ E) ≤ μ.real (B ∆ E) := by
    apply measureReal_mono (h₂ := measure_ne_top μ _)
    intro x hx
    exact Or.inl hx
  have hEBerr : μ.real (E \ B) ≤ μ.real (B ∆ E) := by
    apply measureReal_mono (h₂ := measure_ne_top μ _)
    intro x hx
    exact Or.inr hx
  have hsplitB := measureReal_inter_add_sdiff (μ := μ) (s := B) hE (measure_ne_top μ B)
  have hsplitE := measureReal_inter_add_sdiff (μ := μ) (s := E) hB (measure_ne_top μ E)
  have hmono : μ.real (B ∩ E) ≤ μ.real E := measureReal_mono inter_subset_right (measure_ne_top μ _)
  have hEpos : μ.real B / 2 < μ.real E := by linarith only [hBEerr, herr1, hsplitB, hmono]
  have hinter : μ.real (B ∩ E) = μ.real (E ∩ B) := by rw [inter_comm]
  have hstrict : (1 - δ) * μ.real E < μ.real (B ∩ E) := by
    have hdE : δ * (μ.real B / 2) < δ * μ.real E := mul_lt_mul_of_pos_left hEpos hδ
    nlinarith only [hEBerr, herr2, hsplitE, hinter, hdE]
  have hdisj : Set.PairwiseDisjoint (S : Set (Word A))
      (fun w => cylinder X w (-(n : ℤ))) := by
    intro v hv w hw hvw
    exact disjoint_cylinder X ((hS v hv).2.trans (hS w hw).2.symm) hvw _
  have hdisjB : Set.PairwiseDisjoint (S : Set (Word A))
      (fun w => B ∩ cylinder X w (-(n : ℤ))) := by
    intro v hv w hw hvw
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hdisj hv hw hvw) hx.2 hy.2
  have hsumE : μ.real E = ∑ w ∈ S, μ.real (cylinder X w (-(n : ℤ))) :=
    measureReal_biUnion_finset hdisj (fun w _ => measurableSet_cylinder X w _)
  have hsumB : μ.real (B ∩ E) = ∑ w ∈ S, μ.real (B ∩ cylinder X w (-(n : ℤ))) := by
    have heq : B ∩ E = ⋃ w ∈ S, B ∩ cylinder X w (-(n : ℤ)) := by
      simp only [E, inter_iUnion]
    rw [heq]
    exact measureReal_biUnion_finset hdisjB (fun w _ => hB.inter (measurableSet_cylinder X w _))
  have hex : ∃ w ∈ S, (1 - δ) * μ.real (cylinder X w (-(n : ℤ))) <
      μ.real (B ∩ cylinder X w (-(n : ℤ))) := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_le_sum h
    rw [← hsumB, ← Finset.mul_sum, ← hsumE] at hsum
    exact (not_le_of_gt hstrict) hsum
  obtain ⟨w, hw, hpure⟩ := hex
  refine ⟨w, (hS w hw).1, -(n : ℤ), ?_, hpure⟩
  by_contra hpos
  have hzero : μ.real (cylinder X w (-(n : ℤ))) = 0 :=
    le_antisymm (le_of_not_gt hpos) measureReal_nonneg
  have hsub : μ.real (B ∩ cylinder X w (-(n : ℤ))) ≤
      μ.real (cylinder X w (-(n : ℤ))) := measureReal_mono inter_subset_right (measure_ne_top μ _)
  rw [hzero, mul_zero] at hpure
  rw [hzero] at hsub
  exact (not_le_of_gt hpure) hsub
end BalanceSpecification
