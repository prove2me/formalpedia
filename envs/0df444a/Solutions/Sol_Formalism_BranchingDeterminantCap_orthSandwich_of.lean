-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.orthSandwich_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:29:27.993486+00:00
-- url     : https://prove2.me/submissions/45c59409-b8bd-4f4f-9ffd-4b2352527061

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_rkK_bot
import Theorems.Thm_Formalism_BranchingDeterminantCap_orthogonal_sum_slope
import Theorems.Thm_Formalism_F_orthogonal_sum_slope


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open OrthogonalSumAlt
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (hS : ScaleSandwich) : OrthSandwich := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX S _ A A0 G hA0 hG horth hle hGA
  have hnoeth : IsNoetherian (𝓞 K) A0 := isNoetherian_of_fg_of_noetherian A0 hA0
  have hAfg : ∀ s, (A s).FG := fun s => by
    have := (isNoetherian_submodule.1 hnoeth) (A s) (hle s)
    exact this
  obtain ⟨hrk, hdeg, -⟩ := orthogonal_sum_slope K V ι b X hX S A hAfg horth
  have hB : (⨆ s, A s) ≤ A0 := iSup_le hle
  by_cases h0 : A0 = ⊥
  · have hB0 : (⨆ s, A s) = ⊥ := le_bot_iff.1 (h0 ▸ hB)
    rw [hB0] at hrk hdeg
    rw [← hrk, ← hdeg, h0]
    simp [degD, rkK_bot]
  · obtain ⟨h1, h2, h3, -, -⟩ := hS K V ι b X hX A0 (⨆ s, A s) G hA0 h0 hG hB hGA
    have hr : (0 : ℝ) ≤ (Formalism.HN.rkK A0 : ℝ) := Nat.cast_nonneg _
    refine ⟨by rw [← h1, hrk], ?_, ?_⟩
    · rw [← hdeg, degD, degD, h1]
      exact mul_le_mul_of_nonneg_left h2 hr
    · rw [← hdeg, degD, degD, h1]
      nlinarith [mul_le_mul_of_nonneg_left h3 hr]
end Formalism.BranchingDeterminantCap
