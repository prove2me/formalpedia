-- Prove2me | solution 1 for Formalism.HN.duality_zl_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:21.233801+00:00
-- url     : https://prove2.me/submissions/e053ff0b-b735-4382-91ad-918d16ba42da

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_satR_mem_zl


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
theorem _root_.solution (N : Submodule ℤ E) : zl (AddMonoidHom.id E) N = N := by
  ext y
  rw [satR_mem_zl]
  simp
end Formalism.HN
