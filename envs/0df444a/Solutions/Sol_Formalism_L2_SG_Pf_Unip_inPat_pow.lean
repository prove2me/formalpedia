-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:34.172023+00:00
-- url     : https://prove2.me/submissions/ac6fc840-13c7-49e4-a3c8-70e6a5d8fd8f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_one
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_mul

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
variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (hZ : InPat lv k Z) (m : ℕ) : InPat lv (k * m) (Z ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero, Nat.mul_zero]
    exact inPat_one
  | succ m ih =>
    rw [pow_succ, mul_add_one]
    exact inPat_mul ih hZ
end Formalism.L2.SG.Pf.Unip
