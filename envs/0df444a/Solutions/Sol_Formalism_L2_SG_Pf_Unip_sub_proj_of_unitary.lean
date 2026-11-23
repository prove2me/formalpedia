-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.sub_proj_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:59.888441+00:00
-- url     : https://prove2.me/submissions/83a6eb59-ff4a-45ca-a356-6a960aba4780

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_neg
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_smul
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_mul
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sharp
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_add
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_one
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_mul_self
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
theorem _root_.solution (hJ : Graded lv T J) (hJ' : Graded lv T J') (h : J' * J = 1)
    {x : Matrix ι ι K} (hx : xᴴ * J * x = J) (hx1 : InPat lv k (x - 1)) :
    InPat lv (k + k) ((x - 1) - proj J J' (x - 1)) := by
  obtain ⟨Z, rfl⟩ : ∃ Z, x = Z + 1 := ⟨x - 1, (sub_add_cancel x 1).symm⟩
  rw [add_sub_cancel_right] at hx1 ⊢
  have hA : InPat lv k (sharp J J' Z) := inPat_sharp hJ hJ' hx1
  have h0 := sharp_mul_self h hx
  rw [sharp_add, sharp_one h] at h0
  have e : sharp J J' Z * Z + sharp J J' Z + Z = 0 := by
    have t : sharp J J' Z * Z + sharp J J' Z + Z
        = (sharp J J' Z + 1) * (Z + 1) - 1 := by noncomm_ring
    rw [t, h0, sub_self]
  have hz : -(sharp J J' Z * Z) = sharp J J' Z + Z :=
    neg_eq_iff_add_eq_zero.mpr (by rw [← add_assoc]; exact e)
  have key : Z - proj J J' Z = (⅟2 : K) • -(sharp J J' Z * Z) := by
    rw [hz, proj, smul_sub, smul_add]
    calc Z - ((⅟2 : K) • Z - (⅟2 : K) • sharp J J' Z)
        = ((⅟2 : K) • Z + (⅟2 : K) • Z) - ((⅟2 : K) • Z - (⅟2 : K) • sharp J J' Z) := by
          rw [half_add_half]
      _ = (⅟2 : K) • sharp J J' Z + (⅟2 : K) • Z := by abel
  rw [key]
  exact inPat_smul _ (inPat_neg (inPat_mul hA hx1))
end Formalism.L2.SG.Pf.Unip
