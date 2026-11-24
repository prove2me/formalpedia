-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_trace_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:57.358704+00:00
-- url     : https://prove2.me/submissions/14ada6ba-3157-409d-9faf-70aa19763912

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_trace_pos
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hCM : IsCMUnram K) (a : K) :
    0 ≤ Algebra.trace ℚ K (star a * a) := by
  by_cases ha : a = 0
  · subst ha
    simp
  · exact le_of_lt (massTelescope_trace_pos K hCM a ha)
end Formalism.HermitianLatticesTheory
