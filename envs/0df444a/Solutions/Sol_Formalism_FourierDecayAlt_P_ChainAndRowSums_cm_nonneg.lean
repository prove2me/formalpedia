-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChainAndRowSums.cm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:22.726284+00:00
-- url     : https://prove2.me/submissions/6f4e00c0-16dc-4b70-80c1-8f18142c7658

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_two
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_one

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChainAndRowSums
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.ChainAndRowSums
theorem _root_.solution {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (hc : ∀ n w w', 0 ≤ c n w w') :
    ∀ n w w', 0 ≤ chainMat Wd c n w w' := by
  have : ∀ n, (∀ w w', 0 ≤ chainMat Wd c n w w') ∧ (∀ w w', 0 ≤ chainMat Wd c (n + 1) w w') := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun w w' => ?_, fun w w' => ?_⟩
      · simp only [chainMat]; split_ifs <;> norm_num
      · rw [cm_one]; exact hc 1 w w'
    | succ m ih =>
      refine ⟨ih.2, fun w w' => ?_⟩
      rw [cm_two]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (hc _ _ _) (ih.2 _ _))
  exact fun n => (this n).1
end Formalism.FourierDecayAlt.P.ChainAndRowSums
