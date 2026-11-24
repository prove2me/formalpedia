-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.parameter_choice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:14.18718+00:00
-- url     : https://prove2.me/submissions/e42d827a-f9f3-4fad-b5d3-3d0031ab5da0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_numerical_exclusion_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : ChoiceOfTwoPrimes := by
  intro ε A hε hA
  obtain ⟨x₀, hx₀⟩ := numerical_exclusion_bound ε A hε hA
  refine ⟨x₀, fun x hx r Y GG excl hr hY hGG hexcl => ?_⟩
  obtain ⟨n1, n2⟩ := hx₀ x hx r Y hr hY
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hpos : (0 : ℝ) < (GG.card : ℝ) := by
    have : 0 < Y ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hY0 _
    linarith
  have hne : GG.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
  obtain ⟨g₁, hg₁⟩ := hne
  have hc : (insert g₁ (excl g₁)).card < GG.card := by
    have c1 : (insert g₁ (excl g₁)).card ≤ (excl g₁).card + 1 := Finset.card_insert_le _ _
    have c2 : (((insert g₁ (excl g₁)).card : ℕ) : ℝ) ≤ ((excl g₁).card : ℝ) + 1 := by exact_mod_cast c1
    have c3 := hexcl g₁ hg₁
    have : (((insert g₁ (excl g₁)).card : ℕ) : ℝ) < (GG.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨g₂, hg₂, hg₂'⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  rw [Finset.mem_insert, not_or] at hg₂'
  exact ⟨g₁, hg₁, g₂, hg₂, hg₂'.1, hg₂'.2⟩
end Formalism.HermitianLattices.ZeroFreeRegionGL2
