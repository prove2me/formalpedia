-- Prove2me | solution 1 for BalanceSpecification.blockEntropy_longWordOrbitAverage_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:37.942074+00:00
-- url     : https://prove2.me/submissions/295f0403-9359-4023-af1d-5acdae8dfdf2

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_blockEntropy_translated_add_le
public import Theorems.Thm_BalanceSpecification_blockEntropy_le_alphabet_bound
public import Theorems.Thm_BalanceSpecification_blockEntropy_finiteOrbitProbability_ge
public import Theorems.Thm_BalanceSpecification_blockEntropy_finitePointProbability_representatives
public import Theorems.Thm_BalanceSpecification_translatedProbability_zero
public import Theorems.Thm_BalanceSpecification_blockEntropy_nonneg
public import Theorems.Thm_BalanceSpecification_blocking_estimate
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
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
theorem _root_.solution (hX : X.carrier.Nonempty)
    (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N + 1)
    [Nonempty ↥(wordFinset (language X) (N + 1))]
    (x : ↥(wordFinset (language X) (N + 1)) → X.carrier)
    (hx : ∀ w, block (x w).val 0 (N + 1) = w.val) :
    (n : ℝ) * (Real.log (wordCount (language X) (N + 1)) / ((N + 1 : ℕ) : ℝ)) -
        (3 * (n : ℝ)^2 * Real.log (Fintype.card A)) / ((N + 1 : ℕ) : ℝ) ≤
      blockEntropy (finiteOrbitProbability (shiftMap X) x N) n := by
  have hA : Nonempty A := ⟨hX.choose 0⟩
  let : Nonempty A := hA
  have hC : 0 ≤ Real.log (Fintype.card A) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hb := blocking_estimate (H := fun s l =>
      blockEntropy (translatedProbability (finitePointProbability x) s) l) hC
    (fun s l => blockEntropy_nonneg _ l)
    (fun s a b => blockEntropy_translated_add_le _ s a b)
    (fun s l => blockEntropy_le_alphabet_bound hX _ l) hn hnN
  rw [translatedProbability_zero, blockEntropy_finitePointProbability_representatives (N + 1) x hx] at hb
  have havg := blockEntropy_finiteOrbitProbability_ge x N n
  have hNp : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos N)
  have hsum : (∑ j ∈ Finset.range (N + 1),
      blockEntropy (translatedProbability (finitePointProbability x) j) n) ≤
      ((N + 1 : ℕ) : ℝ) * blockEntropy (finiteOrbitProbability (shiftMap X) x N) n := by
    have hh := mul_le_mul_of_nonneg_left havg hNp.le
    simp only [← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul] at hh
    rw [Fin.sum_univ_eq_sum_range
      (fun j => blockEntropy (translatedProbability (finitePointProbability x) j) n) (N + 1)] at hh
    exact hh
  have hmain : (n : ℝ) * Real.log (wordCount (language X) (N + 1)) -
      (3 * (n : ℝ)^2 * Real.log (Fintype.card A)) ≤
      ((N + 1 : ℕ) : ℝ) * blockEntropy (finiteOrbitProbability (shiftMap X) x N) n := by
    linarith only [hb, hsum]
  have hh := div_le_div_of_nonneg_right hmain hNp.le
  simpa only [sub_div, mul_div_assoc, mul_div_cancel_left₀ _ hNp.ne'] using hh
end BalanceSpecification
