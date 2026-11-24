-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.wal_cT_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:42.479456+00:00
-- url     : https://prove2.me/submissions/a092d25c-233c-4c22-8c95-1a5da541db22

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n]
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (τ : A →+* A) (c : A) (M : Matrix n n A) : cT τ (c • M) = τ c • cT τ M := by
  ext i j; simp [cT]
end Formalism.MainNotions.Gaps.CC.Surj
