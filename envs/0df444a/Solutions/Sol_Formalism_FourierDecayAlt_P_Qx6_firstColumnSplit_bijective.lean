-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.firstColumnSplit_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:43:33.485183+00:00
-- url     : https://prove2.me/submissions/5b998416-58e4-4d8f-b9f2-95f4711448cb

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_firstColumnSplit_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_firstColumnSplit_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (m : ℕ) : Function.Bijective (phi0 m) := by
  have hinj : Function.Injective (phi0 m) := by
    rintro ⟨i, σ⟩ ⟨j, τ⟩ h
    have h0 : i = j := by
      have h1 := congrArg (fun π : Equiv.Perm (Fin (m + 1)) => π 0) h
      simpa only [firstColumnSplit_zero] using h1
    subst h0
    have hs : σ = τ := by
      apply Equiv.ext
      intro k
      have h1 := congrArg (fun π : Equiv.Perm (Fin (m + 1)) => π k.succ) h
      simp only [firstColumnSplit_succ] at h1
      exact Fin.succAbove_right_injective h1
    rw [hs]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  simp [Fintype.card_perm, Fintype.card_prod, Nat.factorial_succ]
end Formalism.FourierDecayAlt.P.Qx6
