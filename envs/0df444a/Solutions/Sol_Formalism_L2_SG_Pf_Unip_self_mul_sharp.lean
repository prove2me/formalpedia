-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.self_mul_sharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:33.406267+00:00
-- url     : https://prove2.me/submissions/e0ec3fee-d210-4a90-8446-d29a33ba52e2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_mul_comm_one
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
variable {lv : ι → ℕ} {T k : ℕ}
variable {J J' : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (h : J' * J = 1) {M : Matrix ι ι K} (hM : Mᴴ * J * M = J) : M * sharp J J' M = 1 := mul_comm_one (sharp_mul_self h hM)
end Formalism.L2.SG.Pf.Unip
