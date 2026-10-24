-- Prove2me | solution 1 for GenNewtonSubgrad.Composite.theorem_5_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:35:26.080965+00:00
-- url     : https://prove2.me/submissions/b502fa06-505f-4bbf-9e83-204e45b5f319
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53
import Theorems.Thm_GenNewtonSubgrad_Composite_theorem_5_7_local

open Filter Topology
open scoped InnerProductSpace

theorem solution {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n))
    (hC11 : GenNewtonSubgrad.ProxReg.IsC11Around φ xbar) (hsol : gradient φ xbar = 0)
    (hH : GenNewtonSubgrad.ProxReg.StandingH (GenNewtonSubgrad.ProxReg.sv (gradient φ)) xbar 0) :
    ∃ U ∈ 𝓝 xbar, GenNewtonSubgrad.ProxReg.Alg53WellDefinedOn φ U ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), GenNewtonSubgrad.ProxReg.IsAlg53Run φ x → x 0 ∈ U → GenNewtonSubgrad.ProxReg.IsQSuperlinear x xbar := by
  obtain ⟨U, hU, hdef, hconv⟩ :=
    GenNewtonSubgrad.Composite.theorem_5_7_local φ xbar hC11 hsol hH Set.univ Filter.univ_mem
  exact ⟨U, hU, fun N x h0 hs => (hdef N x h0 hs).2, hconv⟩
