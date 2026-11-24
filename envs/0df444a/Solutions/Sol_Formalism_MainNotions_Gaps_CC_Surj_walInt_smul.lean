-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.walInt_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:01:59.15991+00:00
-- url     : https://prove2.me/submissions/6287c533-9123-42ec-b225-9e95bed1a4c8

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n]
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (S : Subring A) {c : A} (hc : c ∈ S) {M : Matrix n n A} (hM : walInt S M) :
    walInt S (c • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)
end Formalism.MainNotions.Gaps.CC.Surj
