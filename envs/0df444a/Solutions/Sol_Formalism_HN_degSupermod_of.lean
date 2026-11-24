-- Prove2me | solution 1 for Formalism.HN.degSupermod_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:28.910075+00:00
-- url     : https://prove2.me/submissions/d057e91b-3158-48c1-93e7-1dcc7563e2dd

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Theorems.Thm_Formalism_HN_degSupermod_zl_mono
import Theorems.Thm_Formalism_HN_degSupermod_zl_sup
import Theorems.Thm_Formalism_HN_degSupermod_zl_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w
namespace Formalism.HN
theorem _root_.solution (h : DegSupermodZ.{w}) : DegSupermod.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L A B hL hA hB
  haveI := hL.2
  have key := h E (zl ρ L) (zl ρ A) (zl ρ B) hL.2 (degSupermod_zl_mono ρ hA)
    (degSupermod_zl_mono ρ hB)
  rw [← degSupermod_zl_sup ρ A B, ← degSupermod_zl_inf ρ hL.1 hA hB] at key
  exact key
end Formalism.HN
