-- Prove2me | solution 1 for Formalism.HN.duality_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:22.135917+00:00
-- url     : https://prove2.me/submissions/4cfea513-7c5b-427a-a96c-98d99d6f0984

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_basic
import Theorems.Thm_Formalism_F_att_rk_pos


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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E]
namespace Formalism.HN
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) : dualZ L ≠ ⊥ := by
  intro h
  have h1 := (duality_basic L).2.1
  have h2 := Formalism.F.att_rk_pos hL
  rw [h] at h1
  have h3 : Formalism.F.rk (⊥ : Submodule ℤ E) = 0 := by
    simp [Formalism.F.rk]
  omega
end Formalism.HN
