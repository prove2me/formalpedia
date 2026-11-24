-- Prove2me | solution 1 for BalanceSpecification.exists_invariantGibbs_of_biBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:26.164449+00:00
-- url     : https://prove2.me/submissions/b4e47f56-3ab5-446b-b88e-68a21976b7c6

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_exists_measurePreserving_mapClusterPt_finiteOrbitProbability
public import Theorems.Thm_BalanceSpecification_real_bounds_of_mapClusterPt_of_isClopen
public import Theorems.Thm_BalanceSpecification_finiteOrbitProbability_cylinder_scaled_bounds
public import Theorems.Thm_BalanceSpecification_boundedlySupermultiplicative_of_rightBalanced
public import Theorems.Thm_BalanceSpecification_bsm_iff_wordCount_exp_bound
public import Theorems.Thm_BalanceSpecification_continuous_shiftMap
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_isClosed_cylinder
public import Theorems.Thm_BalanceSpecification_isOpen_cylinder
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty
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
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
namespace BalanceSpecification
theorem _root_.solution
    {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) (hB : BiBalanced (language X)) :
    ∃ μ : ProbabilityMeasure X.carrier, IsGibbsMeasure hX μ := by
  classical
  obtain ⟨⟨cR, hcR, hR⟩, ⟨cL, hcL, hP⟩⟩ := hB
  obtain ⟨C, hC, hupper⟩ := (bsm_iff_wordCount_exp_bound hX).mp
    (boundedlySupermultiplicative_of_rightBalanced (language_factorial X) ⟨cR, hcR, hR⟩)
  have hRscale : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cR * (wordCount (language X) n : ℝ) ≤ (followerFinset (language X) u n).card := by
    intro u hu n hn
    have hp : (0 : ℝ) < wordCount (language X) n := by
      exact_mod_cast wordCount_pos_of_nonempty hX n
    exact (le_div_iff₀ hp).mp (hR u hu n hn)
  have hPscale : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cL * (wordCount (language X) n : ℝ) ≤ (predecessorFinset (language X) u n).card := by
    intro u hu n hn
    have hp : (0 : ℝ) < wordCount (language X) n := by
      exact_mod_cast wordCount_pos_of_nonempty hX n
    exact (le_div_iff₀ hp).mp (hP u hu n hn)
  let W : ℕ → Type _ := fun n => ↥(wordFinset (language X) (3 * (n + 1)))
  have hW (n : ℕ) : (wordFinset (language X) (3 * (n + 1))).Nonempty :=
    Finset.card_pos.mp (wordCount_pos_of_nonempty hX _)
  let : ∀ n, Fintype (W n) := fun _ => inferInstance
  let : ∀ n, Nonempty (W n) := fun n =>
    ⟨⟨(hW n).choose, (hW n).choose_spec⟩⟩
  have hrep : ∀ n (w : W n), ∃ x : X.carrier,
      block x.val 0 (3 * (n + 1)) = w.val := by
    intro n w
    obtain ⟨x, hx, hblock⟩ := mem_language_iff_exists_block_zero.mp
      (mem_wordFinset.mp w.property).1
    refine ⟨⟨x, hx⟩, ?_⟩
    simpa only [(mem_wordFinset.mp w.property).2] using hblock
  choose x hx using hrep
  let : CompactSpace X.carrier := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  obtain ⟨μ, hμ, hμinv⟩ := exists_measurePreserving_mapClusterPt_finiteOrbitProbability
    (continuous_shiftMap X) (fun n w => (shiftMap X)^[n + 1] (x n w))
  have hCp : 0 < C := zero_lt_one.trans_le hC
  let l : ℝ := cL * cR / C
  have hl : 0 < l := div_pos (mul_pos hcL hcR) hCp
  let K : ℝ := max (1 / l) (C * C)
  have hK : 0 < K := (mul_pos hCp hCp).trans_le (le_max_right _ _)
  have hKl : 1 / K ≤ l := by
    calc
      1 / K ≤ 1 / (1 / l) := one_div_le_one_div_of_le (div_pos zero_lt_one hl) (le_max_left _ _)
      _ = l := one_div_one_div l
  refine ⟨μ, hμinv, K, hK, ?_⟩
  intro u hu
  let E := Real.exp ((u.length : ℝ) * entropy X hX)
  have hE : 0 < E := Real.exp_pos _
  have hclopen : IsClopen (cylinder X u 0) :=
    ⟨isClosed_cylinder X u 0, isOpen_cylinder X u 0⟩
  have hevent : ∀ᶠ n : ℕ in atTop,
      l / E ≤
          (finiteOrbitProbability (shiftMap X) (fun w => (shiftMap X)^[n + 1] (x n w)) n :
            Measure X.carrier).real (cylinder X u 0) ∧
      (finiteOrbitProbability (shiftMap X) (fun w => (shiftMap X)^[n + 1] (x n w)) n :
            Measure X.carrier).real (cylinder X u 0) ≤ (C * C) / E := by
    filter_upwards [eventually_ge_atTop u.length] with n hn
    have hbounds := finiteOrbitProbability_cylinder_scaled_bounds hX hcL.le hcR.le hC
      hupper hRscale hPscale n (x n) (hx n) hu (by omega)
    exact ⟨(div_le_iff₀ hE).mpr hbounds.1, (le_div_iff₀ hE).mpr hbounds.2⟩
  have hbounds := real_bounds_of_mapClusterPt_of_isClopen hμ hclopen hevent
  exact ⟨hKl.trans ((div_le_iff₀ hE).mp hbounds.1),
    ((le_div_iff₀ hE).mp hbounds.2).trans (le_max_right _ _)⟩
end BalanceSpecification
