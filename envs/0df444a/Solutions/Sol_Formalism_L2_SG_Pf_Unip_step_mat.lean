-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.step_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:31:40.807918+00:00
-- url     : https://prove2.me/submissions/2a3053bd-f0c3-4d27-892a-f57f0fa165d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_add
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sub
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_sub
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_of_skew
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_proj
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_proj_skew
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sub_proj_of_unitary
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_filtered_mul_mul_sub_sub
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_cay_sub
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_cay_sub_one

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k : ℕ}
variable [StarRing K] [Invertible (2 : K)] {T : ℕ} {J J' : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (hJ : Graded lv T J) (hJ' : Graded lv T J') (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J')
    (h : J' * J = 1) (h' : J * J' = 1) (N : ℕ) {x Y : Matrix ι ι K} (hx : xᴴ * J * x = J)
    (hx1 : InPat lv k (x - 1)) (hY : InPat lv k Y) (hYs : Yᴴ * J = -(J * Y)) :
    InPat lv (k + k) (sharp J J' (cay (N + 1) Y) * x *
      sharp J J' (cay (N + 1) (proj J J' (x - 1) - Y)) - 1) := by
  have hSf : InPat lv k (proj J J' (x - 1)) := inPat_proj hJ hJ' hx1
  have hSY : InPat lv k (proj J J' (x - 1) - Y) := inPat_sub hSf hY
  have hAS : sharp J J' (proj J J' (x - 1)) = -proj J J' (x - 1) :=
    sharp_of_skew h (proj_skew hJh hJ'h h h' (x - 1))
  have t1 := sharp_cay_sub hJ hJ' h N hY
  have t2 := sharp_cay_sub hJ hJ' h N hSY
  have t3 := sub_proj_of_unitary hJ hJ' h hx hx1
  have t4 := filtered_mul_mul_sub_sub (sharp_cay_sub_one hJ hJ' h (N + 1) hY) hx1
    (sharp_cay_sub_one hJ hJ' h (N + 1) hSY)
  have key := inPat_add (inPat_add (inPat_add t4 t1) t2) t3
  rw [sharp_sub, hAS] at key
  convert key using 1
  abel
end Formalism.L2.SG.Pf.Unip
