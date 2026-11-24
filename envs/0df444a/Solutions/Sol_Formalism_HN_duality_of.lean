-- Prove2me | solution 1 for Formalism.HN.duality_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:24.301838+00:00
-- url     : https://prove2.me/submissions/fe892cfa-1c83-406b-bb04-590d2d4ade02

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_basic
import Theorems.Thm_Formalism_HN_duality_ne_bot
import Theorems.Thm_Formalism_HN_duality_muMax

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
universe u
namespace Formalism.HN
theorem _root_.solution (h1 : MuChar.{0, u, u}) : Duality.{u} := by
  intro E _ _ _ L hL
  have := hL
  obtain ⟨hDd, hDr, hDdeg, hDD⟩ := duality_basic L
  refine ⟨hDd, hDr, hDdeg, hDD, fun hL0 => ⟨duality_muMax h1 L hL0, ?_⟩⟩
  have := hDd
  have h := duality_muMax h1 (dualZ L)
    (duality_ne_bot L hL0)
  rw [hDD] at h
  linarith
end Formalism.HN
