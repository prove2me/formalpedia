-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.proj_of_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:32.60436+00:00
-- url     : https://prove2.me/submissions/1c1844f1-6304-4212-b9a3-a973b32b3e3d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_of_skew
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_half_add_half

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
variable [Invertible (2 : K)]
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (h : J' * J = 1) {X : Matrix ι ι K} (hX : Xᴴ * J = -(J * X)) :
    proj J J' X = X := by
  unfold proj
  rw [sharp_of_skew h hX, sub_neg_eq_add, smul_add, half_add_half]
end Formalism.L2.SG.Pf.Unip
