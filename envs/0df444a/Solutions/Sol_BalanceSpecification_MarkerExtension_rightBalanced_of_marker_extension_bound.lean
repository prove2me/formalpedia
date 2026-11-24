-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.rightBalanced_of_marker_extension_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:46.487372+00:00
-- url     : https://prove2.me/submissions/f05bc9ab-94c6-444f-b82a-60e520527d21

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerRight
public import Theorems.Thm_BalanceSpecification_MarkerExtension_exists_source_follower_card_le
public import Theorems.Thm_BalanceSpecification_exp_mul_entropy_le_wordCount
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [TopologicalSpace (Option A)]
  {Y : ShiftSpace A} {X : ShiftSpace (Option A)}
variable [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution
    (hX : X.carrier.Nonempty) (hY : Y.carrier.Nonempty) {C : ℝ} (hC : 0 < C)
    (hUpper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy Y hY))
    (hYRight : RightBalanced (language Y))
    (hmarker : IsSynchronizing (language X) [none])
    (hF : ∀ v ∈ language Y, [none] ++ v.map some ∈ language X)
    (hNonMarker : ∀ u ∈ language X, none ∉ u →
      ∃ v ∈ language Y, u = v.map some) : RightBalanced (language X) := by
  obtain ⟨c, hc, hbound⟩ := hYRight
  refine ⟨c / C, div_pos hc hC, ?_⟩
  intro u hu n hn
  obtain ⟨v, hv, hcard⟩ := exists_source_follower_card_le hmarker hF hNonMarker hu
  have hYpos : (0 : ℝ) < wordCount (language Y) n := by
    exact_mod_cast wordCount_pos_of_nonempty hY n
  have hXpos : (0 : ℝ) < wordCount (language X) n := by
    exact_mod_cast wordCount_pos_of_nonempty hX n
  have hFY := (le_div_iff₀ hYpos).mp (hbound v hv n hn)
  have hcard' : ((followerFinset (language Y) v n).card : ℝ) ≤
      (followerFinset (language X) u n).card := by exact_mod_cast hcard n
  have hlower : c * Real.exp ((n : ℝ) * entropy Y hY) ≤
      (followerFinset (language X) u n).card :=
    (mul_le_mul_of_nonneg_left (exp_mul_entropy_le_wordCount hY n) hc.le).trans
      (hFY.trans hcard')
  apply (div_le_div_iff₀ hC hXpos).mpr
  calc
    c * (wordCount (language X) n : ℝ) ≤
        c * (C * Real.exp ((n : ℝ) * entropy Y hY)) :=
      mul_le_mul_of_nonneg_left (hUpper n) hc.le
    _ = (c * Real.exp ((n : ℝ) * entropy Y hY)) * C := by ring
    _ ≤ ((followerFinset (language X) u n).card : ℝ) * C :=
      mul_le_mul_of_nonneg_right hlower hC.le
end BalanceSpecification.MarkerExtension
