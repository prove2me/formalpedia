-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.superdiag_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:54.928+00:00
-- url     : https://prove2.me/submissions/32de0c63-2a70-42b3-bd14-f6da9f1126a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic
open Finset Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] (k : ℕ)
variable {k}
namespace Formalism.L2.SG.GGMirabolic
theorem _root_.solution : superdiag k (1 : Matrix (Fin k) (Fin k) F) = 0 := by
  unfold superdiag
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · have : i ≠ j := by intro e; subst e; omega
    simp [this]
  · rfl
end Formalism.L2.SG.GGMirabolic
