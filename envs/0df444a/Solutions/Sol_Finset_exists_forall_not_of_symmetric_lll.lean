-- Prove2me | solution 1 for Finset.exists_forall_not_of_symmetric_lll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:05:07.992136+00:00
-- url     : https://prove2.me/submissions/b73b4bfe-aab9-42fb-ae5a-93db14aacbc0

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_bernoulliProb_true
public import Theorems.Thm_Finset_exists_forall_not_of_lll
public import Theorems.Thm_Finset_lopsided_of_dependsOnCoords
public import Theorems.Thm_Finset_bernoulliProb_nonneg

attribute [local simp] Finset.bernoulliProb_true

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
variable {E}
variable {E : ι → Finset α → Prop} [∀ i, DecidablePred (E i)]
namespace Finset
theorem _root_.solution [DecidableEq ι] (h0 : 0 ≤ p) (h1 : p ≤ 1) {I : Finset ι}
    {T : ι → Finset α} (hT : ∀ i ∈ I, T i ⊆ U) (hE : ∀ i ∈ I, DependsOnCoords (E i) (T i)) {q : ℝ}
    {d : ℕ} (hq : ∀ i ∈ I, U.bernoulliProb p (E i) ≤ q)
    (hd : ∀ i ∈ I, #(I.filter fun j => j ≠ i ∧ ¬Disjoint (T i) (T j)) ≤ d)
    (hqd : exp 1 * q * (d + 1) ≤ 1) :
    ∃ A ∈ U.powerset, ∀ i ∈ I, ¬E i A := by
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have he1 : (1 : ℝ) < exp 1 := by
    have := add_one_le_exp (1 : ℝ)
    linarith
  rcases I.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact ⟨∅, empty_mem_powerset _, by simp⟩
  have hq0 : 0 ≤ q := (bernoulliProb_nonneg h0 h1 _).trans (hq i₀ hi₀)
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · -- no dependencies: take `x i = q`
    have hq1 : q < 1 := by
      have : exp 1 * q ≤ 1 := by simpa using hqd
      nlinarith
    refine exists_forall_not_of_lll h0 h1 (lopsided_of_dependsOnCoords hT hE) (x := fun _ => q)
      (fun _ => hq0) (fun _ => hq1) fun i hi => ?_
    rw [card_eq_zero.mp (Nat.le_zero.mp (hd i hi)), prod_empty, mul_one]
    exact hq i hi
  have hd1' : (1 : ℝ) < d + 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    linarith
  refine exists_forall_not_of_lll h0 h1 (lopsided_of_dependsOnCoords hT hE)
    (x := fun _ => 1 / (d + 1))
    (fun _ => by positivity) (fun _ => by rw [div_lt_one hd1]; exact hd1') fun i hi => ?_
  rw [prod_const]
  have hbase : 0 ≤ 1 - 1 / ((d : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one hd1]; linarith
  have hbase1 : 1 - 1 / ((d : ℝ) + 1) ≤ 1 := by
    have : 0 ≤ 1 / ((d : ℝ) + 1) := by positivity
    linarith
  have hpow : (1 - 1 / ((d : ℝ) + 1)) ^ d ≤ (1 - 1 / ((d : ℝ) + 1)) ^ #(I.filter fun j =>
      j ≠ i ∧ ¬Disjoint (T i) (T j)) := pow_le_pow_of_le_one hbase hbase1 (hd i hi)
  -- `(1 - 1/(d+1))^d ≥ e⁻¹`
  have he : (exp 1)⁻¹ ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d := by
    have hinv := one_add_inv_pow_le_exp (n := d)
    have hdpos' : (0 : ℝ) < d := by exact_mod_cast hdpos
    have heq : 1 - 1 / ((d : ℝ) + 1) = (1 + (d : ℝ)⁻¹)⁻¹ := by
      field_simp
      ring
    rw [heq, inv_pow]
    exact inv_anti₀ (by positivity) hinv
  have hqle : q ≤ (exp 1)⁻¹ * (1 / (d + 1)) := by
    rw [inv_mul_eq_div, div_div, le_div_iff₀ (by positivity)]
    linarith
  calc U.bernoulliProb p (E i) ≤ q := hq i hi
    _ ≤ (exp 1)⁻¹ * (1 / (d + 1)) := hqle
    _ ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d * (1 / (d + 1)) :=
        mul_le_mul_of_nonneg_right he (by positivity)
    _ ≤ (1 - 1 / ((d : ℝ) + 1)) ^ #(I.filter fun j => j ≠ i ∧ ¬Disjoint (T i) (T j)) *
          (1 / (d + 1)) := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := mul_comm _ _
end Finset
