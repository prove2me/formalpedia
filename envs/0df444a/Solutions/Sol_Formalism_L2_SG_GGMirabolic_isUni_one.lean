-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.isUni_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:03.818803+00:00
-- url     : https://prove2.me/submissions/35006232-be76-4bd1-8496-bffa2d61b97b

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
theorem _root_.solution : IsUni k (1 : GL (Fin k) F) := by
  refine ⟨fun i => by simp, fun i j hij => ?_⟩
  simp [(ne_of_lt hij).symm]
end Formalism.L2.SG.GGMirabolic
