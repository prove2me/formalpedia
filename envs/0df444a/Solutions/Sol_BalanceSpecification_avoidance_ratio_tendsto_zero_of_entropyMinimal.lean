-- Prove2me | solution 1 for BalanceSpecification.avoidance_ratio_tendsto_zero_of_entropyMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:12.372702+00:00
-- url     : https://prove2.me/submissions/bcdbe144-8f92-4fbe-bfa7-69b7c046f1cc

module
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Theorems.Thm_BalanceSpecification_avoiding_shift_ssubset
public import Theorems.Thm_BalanceSpecification_Growth_ratio_tendsto_zero_of_rate_gap
public import Theorems.Thm_BalanceSpecification_avoidance_ratio_tendsto_zero_of_vanishing
public import Theorems.Thm_BalanceSpecification_exp_mul_entropy_le_wordCount
public import Theorems.Thm_BalanceSpecification_languageEntropy_eq_languageShift
public import Theorems.Thm_BalanceSpecification_languageEntropy_eq_rate
public import Theorems.Thm_BalanceSpecification_languageEntropy_language_eq_entropy
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_wordCount_add_le


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    (hEM : EntropyMinimal X) {v : Word A} (hv : v ∈ language X) :
    Tendsto (fun n : ℕ =>
      (wordCount (avoidingLanguage (language X) v) n : ℝ) / wordCount (language X) n)
      atTop (𝓝 0) := by
  have hX : X.carrier.Nonempty := by
    obtain ⟨x, hx, _, _⟩ := hv
    exact ⟨x, hx⟩
  let D := avoidingLanguage (language X) v
  have hD : IsFactorial D := (language_factorial X).avoidingLanguage v
  by_cases hpos : ∀ n, 0 < wordCount D n
  · have hgap_ext := hEM _ (avoiding_shift_ssubset hv)
    rw [← languageEntropy_eq_languageShift hD,
      languageEntropy_eq_rate hD hpos, languageEntropy_language_eq_entropy hX] at hgap_ext
    have hgap : Growth.rate (fun n => (wordCount D n : ℝ)) < entropy X hX := by
      exact_mod_cast hgap_ext
    have ha : ∀ n, (1 : ℝ) ≤ wordCount D n := fun n => by exact_mod_cast hpos n
    have hsa : Submultiplicative (fun n => (wordCount D n : ℝ)) := by
      intro m n
      change (wordCount D (m + n) : ℝ) ≤ (wordCount D m : ℝ) * (wordCount D n : ℝ)
      exact_mod_cast wordCount_add_le hD m n
    exact Growth.ratio_tendsto_zero_of_rate_gap ha hsa hgap (exp_mul_entropy_le_wordCount hX)
  · obtain ⟨m, hm⟩ := not_forall.mp hpos
    exact avoidance_ratio_tendsto_zero_of_vanishing (language_factorial X) v
      (Nat.eq_zero_of_not_pos hm)
end BalanceSpecification
