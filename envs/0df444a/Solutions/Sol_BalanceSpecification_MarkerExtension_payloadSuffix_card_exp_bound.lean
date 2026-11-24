-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.payloadSuffix_card_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:47.076129+00:00
-- url     : https://prove2.me/submissions/18893372-22ce-45c2-bac2-61cff8886799

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Theorems.Thm_BalanceSpecification_MarkerExtension_monotone_suffixLength
public import Theorems.Thm_BalanceSpecification_MarkerExtension_exists_minimal_payload_index
public import Theorems.Thm_BalanceSpecification_MarkerExtension_remaining_suffix_length_quarter
public import Theorems.Thm_BalanceSpecification_MarkerExtension_payloadSuffix_card_le_wordCount
public import Theorems.Thm_BalanceSpecification_entropy_nonneg


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
variable [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {hY : Y.carrier.Nonempty} {C : ℝ}
    (hC : 0 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy Y hY))
    (hstrict : StrictMono s)
    (hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n)
    (hcofinal : ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ s n) (l : ℕ) :
    ((payloadSuffixFinset M hM x s l).card : ℝ) ≤
      C * Real.exp ((l : ℝ) * entropy Y hY / 4) := by
  obtain ⟨m, hm, hml, hmin⟩ := exists_minimal_payload_index hcofinal l
  have hslarge : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n := by
    intro n hn
    have H := hsize n hn
    omega
  let r := l - min l (suffixLength M s m)
  have hcount : (payloadSuffixFinset M hM x s l).card ≤ wordCount (language Y) r :=
    payloadSuffix_card_le_wordCount M hM x s hslarge (monotone_suffixLength M hstrict) hmin
  have hr : 4 * (r : ℝ) ≤ (l : ℝ) := by
    exact_mod_cast remaining_suffix_length_quarter M s hsize hm hml
  have hscale := mul_le_mul_of_nonneg_right hr (entropy_nonneg hY)
  have hpow : Real.exp ((r : ℝ) * entropy Y hY) ≤
      Real.exp ((l : ℝ) * entropy Y hY / 4) :=
    Real.exp_le_exp.mpr (by nlinarith only [hscale])
  calc
    ((payloadSuffixFinset M hM x s l).card : ℝ) ≤ wordCount (language Y) r := by
      exact_mod_cast hcount
    _ ≤ C * Real.exp ((r : ℝ) * entropy Y hY) := hupper r
    _ ≤ C * Real.exp ((l : ℝ) * entropy Y hY / 4) :=
      mul_le_mul_of_nonneg_left hpow hC
end BalanceSpecification.MarkerExtension
