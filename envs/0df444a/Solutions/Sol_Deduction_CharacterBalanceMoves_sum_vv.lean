-- Prove2me | solution 1 for Deduction.CharacterBalanceMoves.sum_vv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:04.521841+00:00
-- url     : https://prove2.me/submissions/a545d03f-b266-41a9-acef-aa2cd4212d7d

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalanceMoves
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalanceMoves
theorem _root_.solution (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (hKp : ∀ ψ ∈ Kp, ψ ∈ PsiA A0)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (c x : ℝ) :
    ∑ ψ ∈ PsiA A0, vv Kp D ell c x ψ = GmA D ell Kp c x - SigA D ell A0 Kp x := by
  classical
  unfold vv GmA SigA
  rw [Finset.sum_ite, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ψ
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hKp ψ h, h⟩⟩
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ψ
    simp only [Finset.mem_filter, Finset.mem_sdiff]
end Deduction.CharacterBalanceMoves
