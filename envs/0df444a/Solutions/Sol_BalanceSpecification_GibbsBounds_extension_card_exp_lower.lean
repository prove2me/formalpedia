-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.extension_card_exp_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:24.92419+00:00
-- url     : https://prove2.me/submissions/38e2721c-8bb7-4a46-aea4-1e2b33f3746f

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsBalance
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
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
omit [DiscreteTopology A] [BorelSpace A]
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hG : GibbsBounds hX μ K)
    {u : Word A} (hu : u ∈ language X) (n : ℕ)
    (S : Finset (Word A)) (f : Word A → Word A)
    (hwords : ∀ w ∈ S, f w ∈ language X ∧ (f w).length = u.length + n)
    (hsum : (∑ w ∈ S, (μ : Measure X.carrier).real (cylinder X (f w) 0)) =
      (μ : Measure X.carrier).real (cylinder X u 0)) :
    Real.exp ((n : ℝ) * entropy X hX) ≤ K ^ 2 * S.card := by
  let U := Real.exp ((u.length : ℝ) * entropy X hX)
  let E := Real.exp ((n : ℝ) * entropy X hX)
  have hterm : ∀ w ∈ S,
      (μ : Measure X.carrier).real (cylinder X (f w) 0) * U * E ≤ K := by
    intro w hw
    obtain ⟨hwL, hwlen⟩ := hwords w hw
    have H := (hG.2 (f w) hwL).2
    simpa only [hwlen, Nat.cast_add, add_mul, Real.exp_add, ← mul_assoc, U, E] using H
  have hupper : (μ : Measure X.carrier).real (cylinder X u 0) * U * E ≤ S.card * K := by
    calc
      _ = ∑ w ∈ S, (μ : Measure X.carrier).real (cylinder X (f w) 0) * U * E := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ ∑ _w ∈ S, K := Finset.sum_le_sum hterm
      _ = S.card * K := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hlower := mul_le_mul_of_nonneg_right (hG.2 u hu).1 (Real.exp_nonneg ((n : ℝ) * entropy X hX))
  have H : E / K ≤ (S.card : ℝ) * K := by
    have H := hlower.trans hupper
    simpa only [U, E, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
      one_mul] using H
  calc
    E ≤ ((S.card : ℝ) * K) * K := (div_le_iff₀ hG.1).mp H
    _ = K ^ 2 * S.card := by ring
end GibbsBounds
end BalanceSpecification
