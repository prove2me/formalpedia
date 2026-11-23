-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.proj_skew
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:52.211769+00:00
-- url     : https://prove2.me/submissions/f5c9fca6-0895-4fe5-a3dc-7ecd375f2a69

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_star_half

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
theorem _root_.solution (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J') (h : J' * J = 1) (h' : J * J' = 1) (M : Matrix ι ι K) :
    (proj J J' M)ᴴ * J = -(J * proj J J' M) := by
  have e1 : (M - J' * Mᴴ * J)ᴴ * J = -(J * (M - J' * Mᴴ * J)) := by
    have a : J * (M * J') * J = J * M := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_one]
    have b : J * (J' * Mᴴ * J) = Mᴴ * J := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h', Matrix.one_mul]
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJh, hJ'h,
      Matrix.sub_mul, Matrix.mul_sub, a, b, neg_sub]
  unfold proj sharp
  rw [conjTranspose_smul, star_half, smul_mul_assoc, mul_smul_comm, e1, smul_neg]
end Formalism.L2.SG.Pf.Unip
