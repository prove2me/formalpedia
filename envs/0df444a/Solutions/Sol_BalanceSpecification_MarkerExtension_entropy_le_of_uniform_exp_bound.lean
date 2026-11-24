-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.entropy_le_of_uniform_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:16.732534+00:00
-- url     : https://prove2.me/submissions/47dd115a-9300-451f-911c-034e26f59e4a

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Theorems.Thm_BalanceSpecification_exp_mul_entropy_le_wordCount


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [TopologicalSpace A] [DiscreteTopology A] [DiscreteTopology (Option A)]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {Z : ShiftSpace (Option A)}
    (hZ : Z.carrier.Nonempty) {a K : ℝ}
    (hbound : ∀ n : ℕ, (wordCount (language Z) n : ℝ) ≤ K * Real.exp ((n : ℝ) * a)) :
    entropy Z hZ ≤ a := by
  by_contra h
  have hgap : 0 < entropy Z hZ - a := sub_pos.mpr (lt_of_not_ge h)
  have hexp : 1 < Real.exp (entropy Z hZ - a) := Real.one_lt_exp_iff.mpr hgap
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt K hexp
  have H := (exp_mul_entropy_le_wordCount hZ n).trans (hbound n)
  have heq : Real.exp ((n : ℝ) * entropy Z hZ) =
      Real.exp (entropy Z hZ - a) ^ n * Real.exp ((n : ℝ) * a) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at H
  have hle : Real.exp (entropy Z hZ - a) ^ n ≤ K :=
    (mul_le_mul_iff_left₀ (Real.exp_pos ((n : ℝ) * a))).mp H
  exact (not_lt_of_ge hle) hn
end BalanceSpecification.MarkerExtension
