-- Prove2me | solution 1 for Formalism.GM.FockB.step_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:35:41.59494+00:00
-- url     : https://prove2.me/submissions/4f5ef869-6016-4144-b1e6-70a510ed7ea6

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_tieEh_pow_apply
import Theorems.Thm_Formalism_GM_ProjS_fockForm_raiseAug_pow_augLift
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_left
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ}
variable {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.FockB
theorem _root_.solution [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y y' : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y')
    (j : ℕ) :
    M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y') =
      ((j.factorial : k) ^ 2 * (((o + n + r + z + 1 + j - 1).choose j : ℕ) : k) * (z.factorial : k)) *
        M.fockK y (Formalism.GM.tiePhi w e o n z y') := by
  have h := ProjS.fockForm_raiseAug_pow_augLift (z := z) hv hr hy hy' hz hz' j j
  rw [if_pos rfl, ProjS.fockK_smul_left, ProjS.fockK_smul_right, tieEh_pow_apply, tieEh_pow_apply] at h
  have hf : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have h2 : M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y') =
      (j.factorial : k) * ((j.factorial : k) * (((j.factorial : k))⁻¹ * (((j.factorial : k))⁻¹ *
        M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y')))) := by
    field_simp
  rw [h2, h]
  ring
end Formalism.GM.FockB
